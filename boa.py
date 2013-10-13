import operator
import sys
import math
import cmath
import logging
import importlib
from functools import partial
from pprint import pprint
from collections import namedtuple

import edn_format
from edn_format import loads, dumps
from edn_format.edn_lex import Symbol

logging.basicConfig(format="%(asctime)-15s %(msg)s")
logger = logging.getLogger("boa")
logger.setLevel(logging.DEBUG)
logger.addHandler(logging.StreamHandler(sys.stdout))

class Procedure(object):
    "A user-defined Scheme procedure."
    def __init__(self, parms, exp, env):
        self.parms, self.exp, self.env = parms, exp, env

    def __call__(self, *args):
        return eval(self.exp, Env(self.parms, args, self.env))


class Scope(dict):
    """
    An environment: a dict of {'var':val} pairs, with an outer Scope.
    """

    def __init__(self, parms=(), args=(), outer=None):
        # Bind parm list to corresponding args, or single parm to list of args
        self.outer = outer
        if isinstance(parms, Symbol):
            self.update({parms: list(args)})
        else:
            if len(args) != len(parms):
                raise TypeError(
                    "expected {}, given {}".format(
                        dumps(parms),
                        dumps(args)
                    )
                )
            self.update(zip(parms, args))

        self.update(vars(math))
        self.update(vars(cmath))
        self.update(
            {
                '+': operator.add,
                '-': operator.sub,
                'not': operator.not_,
                '>': operator.gt,
                '<': operator.lt,
                '>=': operator.ge,
                '<=': operator.le,
                '=': operator.eq,
                'equal?': operator.eq,
                'eq?': operator.is_,
                'length': len,
                'cons': cons,
                'car': lambda x: x[0],
                'cdr': lambda x: x[1:],
                'append': operator.add,
                'list': lambda *x: list(x),
                'list?': lambda x: isinstance(x, list),
                'null?': lambda x: x == [],
                'symbol?': lambda x: isinstance(x, Symbol),
                'boolean?': lambda x: isinstance(x, bool),
                'pair?': is_pair,
                'port?': lambda x: isinstance(x, file),
                'apply': lambda proc, l: proc(*l),
                'eval': lambda x: eval(expand(x)),
                'load': lambda fn: load(fn),
                'call/cc': callcc,
                'open-input-file': open,
                'close-input-port': lambda p: p.file.close(),
                'open-output-file': lambda f: open(f, 'w'),
                'close-output-port': lambda p: p.close(),
                'eof-object?': lambda x: x is eof_object,
                'read-char': readchar,
                'read': read,
                'write': lambda x, port=sys.stdout: port.write(to_string(x)),
                'display': display,
                'exit': exit
            }
        )


    def find(self, var):
        "Find the innermost Env where var appears."
        if var in self:
            return self
        elif self.outer is None:
            return self.find_missing(var)
        else:
            return self.outer.find(var)

    def find_missing(self, var):
        """
        If we can't find this symbol in the scope look in other files
        or python libraries for it
        """
        logger.debug("'%s' not found in this world, looking in the next", var)
        if "/" in var:
            namespace, attribute = var.split("/")
            logger.debug("Interpreted as %s.%s", namespace, attribute)

            if "py" == namespace:
                return {"py:{}".format(attribute): eval(attribute)}

            else:
                module = importlib.import_module(namespace)

            module_funcs = {
                "{}/{}".format(namespace, k): attr
                for k, attr
                in vars(module).items()
            }
            
            self.update(module_funcs)
            return self

        logger.debug("/ not found")
        raise LookupError(var)



def is_pair(x):
    return x != [] and isa(x, list)


def cons(x, y):
    return [x]+y


def callcc(proc):
    "Call proc with current continuation; escape only"
    ball = RuntimeWarning(
        "Sorry, can't continue this continuation any longer."
    )

    def throw(retval):
        ball.retval = retval
        raise ball

    try:
        return proc(throw)
    except RuntimeWarning as w:
        if w is ball:
            return ball.retval
        else:
            raise w


def readchar(inport):
    "Read the next character from an input port."
    if inport.line != '':
        ch, inport.line = inport.line[0], inport.line[1:]
        return ch
    else:
        return inport.file.read(1) or eof_object


def read(inport):
    """
    Read a Scheme expression from an input port.
    """

    def read_ahead(token):
        if '(' == token:
            L = []
            while True:
                token = inport.next_token()
                if token == ')':
                    return L
                else:
                    L.append(read_ahead(token))

        elif ')' == token:
            raise SyntaxError('unexpected )')

        elif token in quotes:
            return [quotes[token], read(inport)]

        elif token is eof_object:
            raise SyntaxError('unexpected EOF in list')

        else:
            return atom(token)

    # body of read:
    token1 = inport.next_token()
    return eof_object if token1 is eof_object else read_ahead(token1)


def display(x, port=sys.stdout):
    port.write(x if isinstance(x, str) else dumps(x))


global_env = Scope()


def eval(x, env=global_env):
    "Evaluate an expression in an environment."
    while True:
        # variable reference
        if isinstance(x, Symbol):
            logger.debug("Treated as: %s %s", x, 'ovariable reference')
            x = unicode(x)
            return env.find(x)[x]

        # constant literal
        elif not (isinstance(x, list) or isinstance(x, tuple)):
            logger.debug("Treated as: %s %s", x, 'constant literal')
            return x

        # (quote exp)
        elif x[0] is Symbol('quote'):
            logger.debug("Treated as: %s %s", x, 'quote expression')
            (_, exp) = x
            return exp

        # (if test conseq alt)
        elif x[0] is Symbol('if'):
            logger.debug("Treated as: %s %s", x, 'conditional expression')
            (_, test, conseq, alt) = x
            x = (conseq if eval(test, env) else alt)

        # (set! var exp)
        elif x[0] is Symbol('set'):
            logger.debug("Treated as: %s %s", x, 'variable assignment')
            (_, var, exp) = x
            env.find(var)[var] = eval(exp, env)
            return None

        # (define var exp)
        elif x[0] is Symbol('define'):
            logger.debug("Treated as: %s %s", x, 'function definition')
            (_, var, exp) = x
            env[var] = eval(exp, env)
            return None

        # (lambda (var*) exp)
        elif x[0] is Symbol('lambda'):
            logger.debug("Treated as: %s %s", x, 'lambda definition')
            (_, vars, exp) = x
            return Procedure(vars, exp, env)

        # (begin exp+)
        elif x[0] is Symbol('begin'):
            logger.debug("Treated as: %s %s", x, 'begin expression')
            for exp in x[1:-1]:
                eval(exp, env)
            x = x[-1]

        # (proc exp*)
        else:
            logger.debug("Treated as: %s %s", x, 'proc expression')
            exps = [eval(exp, env) for exp in x]
            proc = exps.pop(0)
            if isinstance(proc, Procedure):
                x = proc.exp
                env = Env(proc.parms, exps, proc.env)
            else:
                return proc(*exps)


def file_reader(file_):
    return file_.readline()


def repl(reader):
    while True:
        try:
            exp = reader()
            logger.debug("Received Expression: %s", exp)
            if exp != "":
                pexp = loads(exp)
            else:
                raise EOFError
            result = eval(pexp)
            logger.debug("Evaluated To: %s", dumps(result))
        except (EOFError, KeyboardInterrupt):
            print ""
            exit()
        except Exception as e:
            print 'Interpreter Error, %s: %s' % (type(e).__name__, e)


if len(sys.argv) > 1:
    repl(partial(file_reader, (open(sys.argv[1]))))
else:
    repl(partial(raw_input, "boa> "))
