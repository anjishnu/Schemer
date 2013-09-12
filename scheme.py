"""
CS 61A Project 4, 2012

TA Name: Allen Nguyen

Person A
    Name:Anjishnu
    Login: cs61a-ej
Person B
    Name:Wenyu Zhu
    Login: cs61a-dj
"""

"""This module implements the core Scheme interpreter functions, including the
Eval/Apply mutual recurrence, source code parsing, and the read-eval-print
interactive loop.
"""

import sys
from ucb import main, trace
from scheme_tokens import tokenize_lines, DELIMITERS
from scheme_primitives import *
from buffer import Buffer

##############
# Eval/Apply #
##############

def scheme_eval(expr, env):
    """Evaluate Scheme expression EXPR in enivornment ENV.

    >>> expr = read_line("(+ 2 2)")
    >>> expr
    Pair('+', Pair(2, Pair(2, NULL)))
    >>> scheme_eval(expr, create_global_frame())
    4
    """
    if expr is None:
        raise SchemeError("Cannot evaluate an undefined expression.")

    # Evaluate Atoms
    if scheme_symbolp(expr):
        return env[expr]
    elif scheme_atomp(expr):
        return expr

    # All non-atomic expressions are lists.
    if not scheme_listp(expr):
        raise SchemeError("malformed list: {0}".format(str(expr)))
    first, rest = expr.first, expr.second

    # Evaluate Combinations
    if first in LOGIC_FORMS:
        return scheme_eval(LOGIC_FORMS[first](rest, env), env)
    elif first == "lambda":
        return do_lambda_form(rest, env)
    elif first == "define":
        do_define_form(rest, env)
        return None
    elif first == "quote":
        return do_quote_form(rest)
    elif first == "let":
        expr, env = do_let_form(rest, env)
        return scheme_eval(expr, env)
    elif first == "let*":
        expr, env = do_let_star_form(rest, env)
        return scheme_eval(expr, env)

    else:
        procedure = scheme_eval(first, env)
        args = rest.map(lambda operand: scheme_eval(operand, env))
        return scheme_apply(procedure, args, env)

def scheme_apply(procedure, args, env):
    """Apply scheme PROCEDURE to argument values ARGS in environment ENV."""
    if isinstance(procedure, PrimitiveProcedure):
        arg_list = [arg for arg in args]
        return apply_primitive(procedure, arg_list, env)
    elif isinstance(procedure, LambdaProcedure):
        "*** YOUR CODE HERE ***"
        arg_list = [arg for arg in args]
        new_frame = env.make_call_frame(procedure.formals,args)
        return scheme_eval(procedure.body,new_frame)
    else:
        raise SchemeError("Cannot call {0}".format(repr(procedure)))

def apply_primitive(procedure, arg_list, env):
    """Apply PrimitiveProcedure procedure to Python list arg_list. 

    >>> env = create_global_frame()
    >>> plus = env["+"]
    >>> twos = [2, 2]
    >>> apply_primitive(plus, twos, env)
    4
    >>> add_twos = [read_line("(+ 2 2)")]
    >>> add_twos
    [Pair('+', Pair(2, Pair(2, NULL)))]
    >>> apply_primitive(env["eval"], add_twos, env)
    4
    """

    if procedure.use_env:
        arg_list+=[env]
    try:
        return procedure.fn(*arg_list)
    except TypeError:
        raise SchemeError("Wrong type of argument")
    raise NotImplementedError

################
# Environments #
################

class Frame:
    """An environment frame, representing a mapping from Scheme symbols to
    Scheme values, possibly enclosed within another frame."""

    def __init__(self, parent):
        """An empty frame that is attached to the frame parent."""
        self.inner = {}
        self.parent = parent

    def __getitem__(self, sym):
        return self.find(sym).inner[sym]

    def __repr__(self):
        if self.parent is None:
            return "<Global Frame>"
        else:
            s = sorted('{0}: {1}'.format(k, v) for k, v in self.inner.items())
            return "<{{{0}}} -> {1}>".format(', '.join(s), repr(self.parent))

    def find(self, sym):
        """The environment frame at or parent SELF that defined SYM.  It
        is an error if SYM does not exist."""
        for name in self.inner.keys():
            if name  == sym:
                return self
        if self.parent != None:
            return Frame.find(self.parent,sym)  
        raise SchemeError("unknown identifier: {0}".format(str(sym)))

    def global_frame(self):
        """The global environment at the root of the parent list."""
        e = self
        while e.parent is not None:
            e = e.parent
        return e

    def make_call_frame(self, formals, vals):
        """A new local frame attached to SELF in which the symbols in the
        Scheme formal parameter list FORMALS are bound to the Scheme values in
        the Scheme value list VALS.  FORMALS has either of the formats allowed
        by the check_formals method.  If FORMALS is an ordinary Scheme list,
        then the number of formals must be the same as the number of VALS, and
        each symbol in FORMALS is bound to the corresponding value in VALS.  If
        the last second in FORMALS is a symbol, then the number of values in VALS
        must be at least as large as the number of preceding ("normal") formal
        symbols, and the last formal symbol is bound to a Scheme list
        containing the remaining values in VALS (which may be empty).

        >>> env = create_global_frame()
        >>> formals, vals = read_line("(a b c)"), read_line("(1 2 3)")
        >>> env.make_call_frame(formals, vals)
        <{a: 1, b: 2, c: 3} -> <Global Frame>>
        >>> env.make_call_frame(read_line("(a . b)"), vals)
        <{a: 1, b: (2 3)} -> <Global Frame>>
        """
        frame = Frame(self)
        try:
            len(formals)
            for (key, val) in zip(formals, vals):
                frame.inner[key] = val
        except  SchemeError: 
            frame.inner[formals.first]=vals.first
            frame.inner[formals.second]=vals.second        
        return frame

    def define(self, sym, val):
        """Define Scheme symbol SYM to have value VAL in SELF."""
        self.inner[sym] = val

class LambdaProcedure:
    """A function defined by a lambda expression or the complex define form."""

    def __init__(self, formals, body, env):
        """A function whose formal parameter list is FORMALS (a Scheme list),
        whose body is the single Scheme expression BODY, and whose environment
        is the Frame ENV.  A lambda expression containing multiple expressions,
        such as (lambda (x) (display x) (+ x 1)) can be handled by
        using (begin (display x) (+ x 1)) as the body."""
        self.formals = formals
        self.body = body
        self.env = env

    def __str__(self):
        return "(lambda {0} {1})".format(str(self.formals), str(self.body))

    def __repr__(self):
        args = (self.formals, self.body, self.env)
        return "LambdaProcedure({0}, {1}, {2})".format(*(repr(a) for a in args))

#################
# Special forms #
#################

def do_lambda_form(vals, env):
    """Evaluate a lambda form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    formals = vals[0]
    check_formals(formals)
    "*** YOUR CODE HERE ***"
    arguments = vals.first
    body = vals.second
    if len(body)!=1:
        return LambdaProcedure(arguments,Pair("begin",body),env)
    return LambdaProcedure(arguments,body.first,env)

def do_define_form(vals, env):
    """Evaluate a define form with parameters VALS in environment ENV."""
    check_form(vals, 2)  
    if type(vals.first) == Pair:
        func_name = vals.first.first
        func_args = vals.first.second
        func_body = vals.second
        func = do_lambda_form(Pair(func_args,func_body),env)
        env.inner[func_name] = func
    else:
        rest = vals.second
        value = scheme_eval(rest.first,env)  
        env.inner[vals.first] = value

def do_quote_form(vals):
    """Evaluate a quote form with parameters VALS."""
    check_form(vals, 1, 1)
    return vals[0]

def do_let_form(vals, env):
    """Evaluate a let form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    bindings = vals[0]
    exprs = vals.second
    if not scheme_listp(bindings):
        raise SchemeError("bad bindings list in let form")
    # Add a frame containing bindings
    names, vals = [], []
    try:
        for item in bindings:
            name = item.first
            names += [name]
            vals +=[scheme_eval(item.second.first,env)]
        new_env = env.make_call_frame(names,vals)
    except UnboundLocalError:
        raise SchemeError("unbound variable: "+ name)
    # Evaluate all but the last expression after bindings, and return the last
    last = len(exprs)-1
    for i in range(0, last):
        scheme_eval(exprs[i], new_env)
    return exprs[last], new_env

def do_let_star_form(vals, env):
    """Evaluate a let* form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    bindings = vals[0]
    exprs = vals.second
    if not scheme_listp(bindings):
        raise SchemeError("bad bindings list in let form")
    # Add a frame containing bindings
    names, vals = NULL, NULL
    "*** YOUR CODE HERE ***"
    new_env = env.make_call_frame(names, vals)
    for binding in bindings:
        name = binding[0]
        value = scheme_eval(binding[1],new_env)
        new_env.inner[name]=value

    # Evaluate all but the last expression after bindings, and return the last
    last = len(exprs)-1
    for i in range(0, last):
        scheme_eval(exprs[i], env)
    return exprs[last], env

#########################
# Logical Special Forms #
#########################

def do_if_form(vals, env):
    """Evaluate if form with parameters VALS in environment ENV."""
    check_form(vals, 3, 3)
    "*** YOUR CODE HERE ***"
    condition = vals.first
    result = vals.second
    if_true = result.first
    if_false = result.second.first
    true_false = scheme_eval(condition,env)
    if true_false:
        return if_true
    else:
        return if_false
    return NULL

def do_and_form(vals, env):
    """Evaluate short-circuited and with parameters VALS in environment ENV."""
    for condition in vals:
        if scheme_eval(condition,env)==False:
            return False
    return True

def do_or_form(vals, env):
    """Evaluate short-circuited or with parameters VALS in environment ENV."""
    for condition in vals:
        if scheme_eval(condition,env) != False:
            return True
    return False

def do_cond_form(vals, env):
    """Evaluate cond form with parameters VALS in environment ENV."""
    num_clauses = len(vals)
    for i, clause in enumerate(vals):
        check_form(clause, 1)
        if clause.first == "else":
            if i < num_clauses-1:
                raise SchemeError("else must be last")
            test = True
            if clause.second is NULL:
                raise SchemeError("badly formed else clause")
        else:
            test = scheme_eval(clause.first, env)
        if test:
            "*** YOUR CODE HERE ***"
            if len(clause.second)>1:
                return scheme_eval(Pair('begin',clause.second),env)
            elif len(clause.second) == 1:
                return scheme_eval(clause.second.first,env)
            else:
                return True
    return None
        

def do_begin_form(vals, env):
    """Evaluate begin form with parameters VALS in environment ENV."""
    check_form(vals, 1)
    "*** YOUR CODE HERE ***"
    i = 0
    length = len(vals)
    for statement in vals:
        i+=1
        if i == len(vals)-1:
            return vals[i]
        else:
            scheme_eval(statement,env)
    

def do_case_form(vals, env):
    """Evaluate case form with parameters VALS in environment ENV."""
    return False

LOGIC_FORMS = {
        "and": do_and_form,
        "or": do_or_form,
        "if": do_if_form,
        "cond": do_cond_form,
        "begin": do_begin_form,
        "case": do_case_form
        }

# Utility methods for checking the structure of Scheme programs

def check_form(expr, min, max = None):
    """Check EXPR (default SELF.expr) is a proper list whose length is
    at least MIN and no more than MAX (default: no maximum). Raises
    a SchemeError if this is not the case."""
    if not scheme_listp(expr):
        raise Exception("badly formed expression: %s", expr)
    length = len(expr)
    if length < min:
        raise SchemeError("too few operands in form")
    elif max is not None and length > max:
        raise SchemeError("too many operands in form")

def check_formals(formals):
    """Check that FORMALS is a valid parameter list having either the form
    symrest OR (sym1 sym2 ... symn) OR (sym1 sym2 ... symn . symrest), where each
    symX is a distinct symbol.

    >>> check_formals(read_line("(a b c)"))
    >>> check_formals(read_line("(a b . c)"))
    >>> check_formals("a")
    """
    args = []
    if type(formals) == Pair:
        while type(formals.second) == Pair:
            if type(formals.first)== Pair:
                raise SchemeError("formal arguments cannot be pair")
            if scheme_symbolp(formals.first):
                if formals.first in args:
                    raise SchemeError("formal arguments cannot have the same name")
                if scheme_numberp(formals.first):
                    raise SchemeError("formal arguments cannot be number")
            args+=formals.first
            formals = formals.second
    else:
        if scheme_numberp(formals):
            raise SchemeError("formal arguments cannot be number")
                         

################
# Input/Output #
################

def scheme_read(input_port):
    """Read the next expression from INPUT_PORT, a buffer.Buffer.

    >>> scheme_read(Buffer(tokenize_lines(["(1", "2 .", "'(3 4))", "4"])))
    Pair(1, Pair(2, Pair('quote', Pair(Pair(3, Pair(4, NULL)), NULL))))
    """
    def read_tail():
        """Assuming that input is positioned inside a Scheme list or pair,
        immediately before a final parenthesis or another item in the list,
        return the remainder of the list from that point.  Thus, returns
        (2 3) when positioned at the carat in "(1 ^ 2 3)", returns nil when
        positioned at the carat in "(1 2 3 ^ )", and returns the pair (2 . 3)
        when positioned at the carat in (1 ^ 2 . 3).
        """
        if input_port.current() is None:
            raise SchemeError("unexpected end of file")
        if input_port.current() == ')':
            input_port.pop()
            return NULL
        if input_port.current() == ".":
            input_port.pop()
            a = read_tail()
            if len(a)!=1:
                raise SchemeError("too many elements in pair")
            return a.first
        result = Pair(scheme_read(input_port),read_tail())
        return result

    if input_port.current() is None:
        return EOF
    val = input_port.pop()
    if scheme_atomp(val) and val not in DELIMITERS:
        return val
    elif val == "'":
        return Pair("quote", Pair(scheme_read(input_port), NULL))
    elif val == "(":
        return read_tail()
    else:
        raise SchemeError("unexpected token: {0}".format(val))

def read_eval_print(input_port, prompt, env, print_input):
    """Read and evaluate from the current input port until the end of file.
    If PROMPT is not None, use it to prompt for input and print values of
    each expression."""
    while True:
        try:
            if prompt is not None:
                print(prompt, end = "")
            sys.stdout.flush()
            expr = scheme_read(input_port)
            if expr is EOF:
                return
            if print_input:
                print(expr)
            val = scheme_eval(expr, env)
            if prompt is not None and val is not None:
                scheme_display(val)
                scheme_newline()
        except SchemeError as exc:
            if not exc.args[0]:
                print("Error", file=sys.stderr)
            else:
                print("Error: {0}".format(exc.args[0]), file=sys.stderr)
            sys.stderr.flush()

def scheme_load(sym, env):
    """Load Scheme source file SYM."""
    check_type(sym, scheme_symbolp, 0, "load")
    with scheme_open(filename) as inp:
        scheme_repl(inp, "", env.global_frame(), False)

def scheme_repl(source, prompt, env, print_input=True):
    """Start a read-eval-print loop reading from SOURCE."""
    read_eval_print(Buffer(tokenize_lines(source)), prompt, env, print_input)

def scheme_open(filename):
    """If either FILENAME or FILENAME.scm is the name of a valid file,
    return a Python file opened to it. Otherwise, raise an error."""
    try:
        return open(filename)
    except IOError as exc:
        if filename.endswith('.scm'):
            raise SchemeError(str(exc))
    try:
        return open(filename + '.scm')
    except IOError as exc:
        raise SchemeError(str(exc))

def read_line(line):
    """Read a single string LINE as a Scheme expression."""
    return scheme_read(Buffer(tokenize_lines([line])))

def create_global_frame():
    """Initialize and return a single-frame environment with built-in names."""
    env = Frame(None)
    env.define("eval", PrimitiveProcedure(scheme_eval, True))
    env.define("apply", PrimitiveProcedure(scheme_apply, True))
    env.define("load", PrimitiveProcedure(scheme_load, True))
    add_primitives(env)
    return env

@main
def run(*argv):
    if argv:
        try:
            input_file = open(argv[0])
            print_input = True
        except IOError as exc:
            print("could not open {0}: {1}".format(argv[0], exc.args[0]),
                  file=sys.stderr)
            sys.exit(1)
    else:
        input_file = sys.stdin
        print_input = False

    scheme_repl(input_file, "scm> ", create_global_frame(), print_input)
