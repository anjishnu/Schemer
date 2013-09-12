"""This module implements the data types and primitives of the Scheme language.

In addition to the types defined in this file, some data types in Scheme are
represented by their corresponding type in Python:
    number:       int or float
    symbol:       string
    boolean:      bool
    unspecified:  None

The __repr__ method of a Scheme value will return a Python expression that
would be evaluated to the value, where possible.

The __str__ method of a Scheme value will return a Scheme expression that
would be read to the value, where possible.
"""

import math
import operator
import sys

try:
    import turtle
except:
    print("warning: could not import the turtle module.", file=sys.stderr)


#################
# Scheme Values #
#################

class SchemeError(BaseException):
    """Exception indicating an error in a Scheme program."""

class Pair:
    """A pair has two elements, first and rest.  If the Pair is a well-formed
    list, rest is either a list or NULL.  Some methods only apply to lists.
    """
    def __init__(self, first, second):
        self.first = first
        self.second = second

    def __repr__(self):
        return "Pair({0}, {1})".format(repr(self.first), repr(self.second))

    def __str__(self):
        s = "(" + str(self.first)
        second = self.second
        while isinstance(second, Pair):
            s += " " + str(second.first)
            second = second.second
        if second is not NULL:
            s += " . " + str(second)
        return s + ")"

    def __len__(self):
        n, second = 1, self.second
        while isinstance(second, Pair):
            n += 1
            second = second.second
        if second is not NULL:
            raise SchemeError("length attempted on improper list")
        return n

    def __getitem__(self, k):
        if k < 0:
            raise SchemeError("negative index into list")
        y = self
        for _ in range(k):
            if y.second is NULL:
                raise SchemeError("list index out of bounds")
            elif not isinstance(y.second, Pair):
                raise SchemeError("ill-formed list")
            y = y.second
        return y.first

    def __iter__(self):
        y = self
        while y is not NULL:
            yield y.first
            y = y.second

    def map(self, fn):
        """Return a Scheme list after mapping Python function FN to SELF."""
        mapped = fn(self.first)
        if self.second is NULL or isinstance(self.second, Pair):
            return Pair(mapped, self.second.map(fn))
        else:
            raise SchemeError("ill-formed list")

class NULL:
    """The empty list"""

    def __str__(self):
        return "nil"

    def __repr__(self):
        return "NULL"

    def __len__(self):
        return 0

    def __getitem__(self, k):
        if k < 0:
            raise SchemeError("negative index into list")
        raise SchemeError("list index out of bounds")

    def __iter__(self):
        return iter(tuple())

    def map(self, fn):
        return self

NULL = NULL() # Assignment hides the NULL class; there is only one instance

class EOF:
    """Represents an end-of-file condition when reading."""

    def __str__(self):
        return "<EOF>"

    def __repr__(self):
        return "EOF"

EOF = EOF()

########################
# Primitive Operations #
########################

class PrimitiveProcedure:
    """A Scheme procedure defined as a Python function."""

    def __init__(self, fn, use_env=False):
        self.fn = fn
        self.use_env = use_env

_PRIMITIVES = []

def primitive(*names):
    """An annotation to convert a Python function into a PrimitiveProcedure."""
    def add(fn):
        proc = PrimitiveProcedure(fn)
        for name in names:
            _PRIMITIVES.append((name,proc))
        return fn
    return add

def add_primitives(frame):
    """Enter bindings in _PRIMITIVES into FRAME, an environment frame."""
    for name, proc in _PRIMITIVES:
        frame.define(name, proc)

def check_type(val, predicate, k, name):
    """Returns VAL.  Raises a SchemeError if not PREDICATE(VAL)
    using "argument K of NAME" to describe the offending value."""
    if not predicate(val):
        msg = "argument {0} of {1} has wrong type ({2})"
        raise SchemeError(msg.format(k, name, type(val).__name__))
    return val

@primitive("boolean?")
def scheme_booleanp(x):
    return x is True or x is False

def scheme_true(val):
    """All values in Scheme are true except False."""
    return val is not False

@primitive("not")
def scheme_not(x):
    return not scheme_true(x)

@primitive("eq?")
def scheme_eqp(x, y):
    return x == y

@primitive("pair?")
def scheme_pairp(x):
    return isinstance(x, Pair)

@primitive("null?")
def scheme_nullp(x):
    return x is NULL

@primitive("list?")
def scheme_listp(x):
    """Return whether x is a well-formed list. Assumes no cycles."""
    while x is not NULL:
        if not isinstance(x, Pair):
            return False
        x = x.second
    return True

@primitive("length")
def scheme_length(x):
    if x is NULL:
        return 0
    check_type(x, scheme_listp, 0, 'length')
    return len(x)

@primitive("cons")
def scheme_cons(x, y):
    return Pair(x, y)

@primitive("car")
def scheme_car(x):
    check_type(x, scheme_pairp, 0, 'car')
    return x.first

@primitive("cdr")
def scheme_cdr(x):
    check_type(x, scheme_pairp, 0, 'cdr')
    return x.second

@primitive("list")
def scheme_list(*vals):
    result = NULL
    for i in range(len(vals)-1, -1, -1):
        result = Pair(vals[i], result)
    return result

@primitive("append")
def scheme_append(*vals):
    if len(vals) == 0:
        return NULL
    result = vals[-1]
    for i in range(len(vals)-2, -1, -1):
        v = vals[i]
        if v is not NULL:
            check_type(v, scheme_pairp, i, "append")
            r = p = Pair(v.first, result)
            v = v.second
            while scheme_pairp(v):
                p.second = Pair(v.first, result)
                p = p.second
                v = v.second
            result = r
    return result

@primitive("symbol?")
def scheme_symbolp(x):
    return isinstance(x, str)

@primitive("number?")
def scheme_numberp(x):
    return isinstance(x, int) or isinstance(x, float)

@primitive("integer?")
def scheme_integerp(x):
    return isinstance(x, int) or round(x) == x

def _check_nums(*vals):
    """Check that all arguments in VALS are numbers."""
    for i, v in enumerate(vals):
        if not scheme_numberp(v):
            msg = "operand {0} ({1}) is not a number"
            raise SchemeError(msg.format(i, v))

def _arith(fn, init, vals):
    """Perform the fn fneration on the number values of VALS, with INIT as
    the value when VALS is empty. Returns the result as a Scheme value."""
    _check_nums(*vals)
    s = init
    for val in vals:
        s = fn(s, val)
    if round(s) == s:
        s = round(s)
    return s

@primitive("+")
def scheme_add(*vals):
    return _arith(operator.add, 0, vals)

@primitive("-")
def scheme_sub(val0, *vals):
    if len(vals) == 0:
        return -val0
    return _arith(operator.sub, val0, vals)

@primitive("*")
def scheme_mul(*vals):
    return _arith(operator.mul, 1, vals)

@primitive("/")
def scheme_div(val0, val1):
    return _arith(operator.truediv, val0, [val1])

@primitive("quotient")
def scheme_quo(val0, val1):
    return _arith(operator.floordiv, val0, [val1])

@primitive("modulo", "remainder")
def scheme_modulo(val0, val1):
    return _arith(operator.mod, val0, [val1])

@primitive("floor")
def scheme_floor(val):
    _check_nums(val)
    return math.floor(val)

@primitive("ceil")
def scheme_ceil(val):
    _check_nums(val)
    return math.ceil(val)

def _numcomp(op, x, y):
    _check_nums(x, y)
    return op(x, y)

@primitive("=")
def scheme_eq(x, y):
    return _numcomp(operator.eq, x, y)

@primitive("<")
def scheme_lt(x, y):
    return _numcomp(operator.lt, x, y)

@primitive(">")
def scheme_gt(x, y):
    return _numcomp(operator.gt, x, y)

@primitive("<=")
def scheme_le(x, y):
    return _numcomp(operator.le, x, y)

@primitive(">=")
def scheme_ge(x, y):
    return _numcomp(operator.ge, x, y)

##
## Other operations
##

@primitive("atom?")
def scheme_atomp(x):
    if scheme_booleanp(x):
        return True
    if scheme_numberp(x):
        return True
    if scheme_symbolp(x):
        return True
    if scheme_nullp(x):
        return True
    return False

@primitive("eof?")
def scheme_eof_objectp(x):
    return x is EOF

@primitive("display")
def scheme_display(val):
    print(str(val), end="")

@primitive("newline")
def scheme_newline():
    print()
    sys.stdout.flush()

@primitive("error")
def scheme_error(msg = None):
    msg = "" if msg is None else str(msg)
    raise SchemeError(msg)

@primitive("exit")
def scheme_exit():
    sys.exit(0)

##
## Turtle graphics (non-standard)
##

_turtle_screen_on = False

def _tscheme_prep():
    global _turtle_screen_on
    if not _turtle_screen_on:
        _turtle_screen_on = True
        turtle.title("Scheme Turtles")
        turtle.mode('logo')

@primitive("forward", "fd")
def tscheme_forward(n):
    """Move the turtle forward a distance N units on the current heading."""
    _check_nums(n)
    _tscheme_prep()
    turtle.forward(n)

@primitive("backward", "back", "bk")
def tscheme_backward(n):
    """Move the turtle backward a distance N units on the current heading,
    without changing direction."""
    _check_nums(n)
    _tscheme_prep()
    turtle.backward(n)

@primitive("left", "lt")
def tscheme_left(n):
    """Rotate the turtle's heading N degrees counterclockwise."""
    _check_nums(n)
    _tscheme_prep()
    turtle.left(n)

@primitive("right", "rt")
def tscheme_right(n):
    """Rotate the turtle's heading N degrees clockwise."""
    _check_nums(n)
    _tscheme_prep()
    turtle.right(n)

@primitive("circle")
def tscheme_circle(r, extent = None):
    """Draw a circle with center R units to the left of the turtle (i.e.,
    right if N is negative.  If EXTENT is not None, then draw EXTENT degrees
    of the circle only.  Draws in the clockwise direction if R is negative,
    and otherwise counterclockwise, leaving the turtle facing along the
    arc at its end."""
    if extent is None:
        _check_nums(r)
    else:
        _check_nums(r, extent)
    _tscheme_prep()
    turtle.circle(r, extent and extent)

@primitive("setposition", "setpos", "goto")
def tscheme_setposition(x, y):
    """Set turtle's position to (X,Y), heading unchanged."""
    _check_nums(x, y)
    _tscheme_prep()
    turtle.setposition(x, y)

@primitive("setheading", "seth")
def tscheme_setheading(h):
    """Set the turtle's heading H degrees clockwise from north (up)."""
    _check_nums(h)
    _tscheme_prep()
    turtle.setheading(h)

@primitive("penup", "pu")
def tscheme_penup():
    """Raise the pen, so that the turtle does not draw."""
    _tscheme_prep()
    turtle.penup()

@primitive("pendown", "pd")
def tscheme_pendown():
    """Lower the pen, so that the turtle starts drawing."""
    _tscheme_prep()
    turtle.pendown()

@primitive("showturtle", "st")
def tscheme_showturtle():
    """Make turtle visible."""
    _tscheme_prep()
    turtle.showturtle()

@primitive("hideturtle", "ht")
def tscheme_hideturtle():
    """Make turtle visible."""
    _tscheme_prep()
    turtle.hideturtle()

@primitive("clear")
def tscheme_clear():
    """Clear the drawing, leaving the turtle unchanged."""
    _tscheme_prep()
    turtle.clear()

@primitive("color")
def tscheme_color(c):
    """Set the color to C, a symbol such as red or '#ffc0c0' (representing
    hexadecimal red, green, and blue values."""
    _tscheme_prep()
    check_type(c, Symbol, 0, "color")
    turtle.color(str(c))

@primitive("begin_fill")
def tscheme_begin_fill():
    """Start a sequence of moves that outline a shape to be filled."""
    _tscheme_prep()
    turtle.begin_fill()

@primitive("end_fill")
def tscheme_end_fill():
    """Fill in shape drawn since last begin_fill."""
    _tscheme_prep()
    turtle.end_fill()

@primitive("exitonclick")
def tscheme_exitonclick():
    """Wait for a click on the turtle window, and then close it."""
    global _turtle_screen_on
    if _turtle_screen_on:
        turtle.exitonclick()
        _turtle_screen_on = False

@primitive("speed")
def tscheme_speed(s):
    """Set the turtle's animation speed as indicated by S (an integer in
    0-10, with 0 indicating no animation (lines draw instantly), and 1-10
    indicating faster and faster movement."""
    check_type(s, scheme_integerp, 0, "speed")
    _tscheme_prep()
    turtle.speed(s)
