import keyword
import token
from tokenize import generate_tokens
import tokenize
from funcparserlib.parser import some, many, skip, maybe, \
    with_forward_decls, NoParseError, Parser


__all__ = ['file_input', 'parse_file']


class CustomParseError(Exception):
    def __init__(self, msg, orig_error):
        self.msg = msg
        self.orig_error = orig_error


def op_(s):
    return some(lambda tok: tok.type == token.OP and tok.string == s)


def s_(string):
    return skip(some(lambda tok: tok.type == token.OP and tok.string == string))


def name_(string):
    return skip(
        some(lambda tok: tok.type == token.NAME and tok.string == string))


INDENT = some(lambda tok: tok.type == token.INDENT)
DEDENT = some(lambda tok: tok.type == token.DEDENT)
NEWLINE = skip(
    some(lambda tok: tok.type == tokenize.NL or tok.type == token.NEWLINE))
ENDMARKER = skip(some(lambda tok: tok.type == token.ENDMARKER))
COMMENT = some(lambda tok: tok.type == tokenize.COMMENT)
NUMBER = some(lambda tok: tok.type == token.NUMBER)
NAME = some(lambda tok: tok.type == token.NAME)
IDENTIFIER = some(
    lambda tok: tok.type == token.NAME and not keyword.iskeyword(tok.string))
STRING = some(lambda tok: tok.type == token.STRING)
ELLIPSIS = skip(some(
    lambda tok: tok.type == token.ELLIPSIS or (
                tok.type == token.OP and tok.string == '...')))


# Keywords
AND = skip(name_('and'))
AS = skip(name_('as'))
ASSERT = skip(name_('assert'))
AWAIT = skip(some(lambda tok: tok.type == token.AWAIT))
ASYNC = skip(some(lambda tok: tok.type == token.ASYNC))
BREAK = skip(name_('break'))
CLASS = skip(name_('class'))
CONTINUE = skip(name_('continue'))
DEF = skip(name_('def'))
DEL = skip(name_('del'))
ELIF = skip(name_('elif'))
ELSE = skip(name_('else'))
EXCEPT = skip(name_('except'))
FALSE = skip(name_('False'))
FINALLY = skip(name_('finally'))
FROM = skip(name_('from'))
FOR = skip(name_('for'))
GLOBAL = skip(name_('global'))
IF = skip(name_('if'))
IMPORT = skip(name_('import'))
IN = skip(name_('in'))
IS = skip(name_('is'))
LAMBDA = skip(name_('lambda'))
NONLOCAL = skip(name_('nonlocal'))
NOT = skip(name_('not'))
OR = skip(name_('or'))
PASS = skip(name_('pass'))
RAISE = skip(name_('raise'))
RETURN = skip(name_('return'))
TRY = skip(name_('try'))
WHILE = skip(name_('while'))
WITH = skip(name_('with'))
YIELD = skip(name_('yield'))

ASSIGN = op_('=')
COLON = op_(':')
COMMA = op_(',')
DOT = op_('.')
TO = op_('->')
SEMI = op_(';')
STAR = op_('*')
SSTAR = op_('**')

NONE = name_('None')
TRUE = name_('True')


# helpers
def sep_by(parser, sep=COMMA, trailing=True):
    """Parses one or more instances of p separated by sep."""
    p = parser + many(sep + parser)
    if trailing:
        p += maybe(sep)
    return p


def choice(parsers):
    """Return a parser which is a choice (|) of the input parsers."""
    p = None
    for parser in parsers:
        if p is None:
            p = parser
        else:
            p = p | parser
    return p


def between(parser, left=op_('('), right=op_(')'), empty=False):
    """Return a parser that parses an occurrence of parser between left and
    right.

    Can omit parser if empty is True."""
    if empty:
        return left + maybe(parser) + right
    else:
        return left + parser + right


def one_plus(p):
    """Parser(a, b) -> Parser(a, [b])

    Return a parser that applies the parser p one or more times.
    """
    q = p + many(p)
    return q.named('(%s , { %s })' % (p.name, p.name))


def try_(p, msg):
    """Parser(a, b) -> Parser(a, b)

    Return a parser that tries to parse p, and raises a CustomParseError
    when it fails.
    """
    @Parser
    def _try_p(tokens, s):
        try:
            return p.run(tokens, s)
        except NoParseError as err:
            raise CustomParseError(msg, err)

    return _try_p


# Grammar starts here
test = with_forward_decls(lambda: choice([
    or_test + maybe(IF + or_test + ELSE + test),
    lambdef]))
not_test = with_forward_decls(lambda: (NOT + not_test) | comparison)
and_test = sep_by(not_test, AND)
or_test = sep_by(and_test, OR)
test_nocond = with_forward_decls(lambda: or_test | lambdef_nocond)
testlist = with_forward_decls(lambda: sep_by(test))


atom = with_forward_decls(lambda: choice([
    between(yield_expr | testlist_comp, empty=True),
    between(testlist_comp, op_('['), op_(']'), empty=True),
    between(dictorsetmaker, op_('{'), op_('}'), empty=True),
    IDENTIFIER,
    NUMBER,
    STRING + many(STRING),
    ELLIPSIS,
    NONE,
    TRUE,
    FALSE
]))


sliceop = COLON + maybe(test)
subscript = test | (maybe(test) + COLON + maybe(test) + maybe(sliceop))
subscriptlist = sep_by(subscript)
trailer = with_forward_decls(lambda: choice([
    between(arglist, empty=True),
    between(subscriptlist, op_('['), op_(']'), empty=True),
    op_('.') + NAME]))

atom_expr = maybe(AWAIT) + atom + many(trailer)
power = with_forward_decls(lambda: atom_expr + maybe(s_('**') + factor))
factor = many(s_('+') | s_('-') | s_('~')) + power
term = sep_by(factor, s_('*') | s_('@') | s_('/') | s_('%') | s_('//'))
arith_expr = sep_by(term, op_('+') | op_('-'))
shift_expr = sep_by(arith_expr, s_('<<') | s_('>>'))
and_expr = sep_by(shift_expr, s_('&'))
xor_expr = sep_by(and_expr, s_('^'))
expr = sep_by(xor_expr, s_('|'))

comp_op = choice([
    op_('<'), op_('>'), op_('=='), op_('>='), op_('<='), op_('<>'), op_('!='),
    IN, NOT + IN, IS + NOT, IS,])
comparison = sep_by(expr, comp_op, trailing=False)

star_expr = STAR + expr
exprlist = sep_by(expr | star_expr)

yield_arg = (FROM + test) | testlist
yield_expr = YIELD + maybe(yield_arg)

comp_iter = with_forward_decls(lambda: comp_for | comp_if)
comp_for = maybe(ASYNC) + FOR + exprlist + IN + or_test + maybe(comp_iter)
comp_if = IF + test_nocond + maybe(comp_iter)

testlist_comp = (
    (test | star_expr) +
    (comp_for | many(COMMA + (test | star_expr)) + maybe(COMMA))
)

_dict_element = (test + COLON + test) | (SSTAR + expr)
_dictmaker = _dict_element + (comp_for |
                              (many(COMMA + _dict_element) + maybe(COMMA)))

_set_element = test | star_expr
_setmaker = _set_element + (comp_for |
                            (many(COMMA + _set_element) + maybe(COMMA)))
dictorsetmaker = _dictmaker | _setmaker


## Simple statements
assert_stmt = ASSERT + test + maybe(COMMA + test)
break_stmt = BREAK
continue_stmt = CONTINUE
del_stmt = DEL + exprlist
global_stmt = GLOBAL + sep_by(NAME, trailing=False)
nonlocal_stmt = NONLOCAL + sep_by(NAME, trailing=False)
pass_stmt = PASS
return_stmt = RETURN + maybe(testlist)
raise_stmt = RAISE + maybe(test + maybe(FROM + test))
yield_stmt = yield_expr
flow_stmt = choice([break_stmt, continue_stmt, return_stmt,
                    raise_stmt, yield_stmt])

annassign = COLON + test + maybe(ASSIGN + test)
testlist_star_expr = sep_by(test | star_expr)
augassign = (
    op_('+=') | op_('-=') | op_('*=') | op_('@=') | op_('/=') | op_('%=') |
    op_('&=') | op_('|=') | op_('^=') | op_('<<=') | op_('>>=') | op_('**=') |
    op_('//=')
)

expr_stmt = testlist_star_expr + choice([
    annassign,
    augassign + (yield_expr | testlist),
    many(ASSIGN + (yield_expr | testlist_star_expr))
])

## Imports
dotted_name = sep_by(IDENTIFIER, DOT, trailing=False)
dotted_as_name = dotted_name + maybe(AS + IDENTIFIER)
dotted_as_names = sep_by(dotted_as_name, trailing=False)
import_name = IMPORT + dotted_as_names

import_as_name = IDENTIFIER + maybe(AS + IDENTIFIER)
import_as_names = sep_by(import_as_name)
import_from = (
    FROM +
    ((many(DOT | ELLIPSIS) + dotted_name) | one_plus(DOT | ELLIPSIS)) +
    IMPORT +
    choice([STAR, between(import_as_names), import_as_names])
)
import_stmt = import_name | import_from

## COMPOUND STATEMENTS
suite = with_forward_decls(lambda: choice([
    simple_stmt,
    # Had to add in a "NEWLINE" token
    NEWLINE + INDENT + stmt + many(stmt) + maybe(NEWLINE) + DEDENT]))
if_stmt = (
    IF + test + try_(COLON, 'missing colon after if condition') + suite +
    many(ELIF + test + try_(COLON, 'missing colon after elif condition') + suite) +
    maybe(ELSE + try_(COLON, 'missing colon after else') + suite)
)
while_stmt = WHILE + test + COLON + suite + maybe(ELSE + COLON + suite)
for_stmt = FOR + exprlist + IN + testlist + COLON + suite + maybe(
    ELSE + COLON + suite)
except_clause = EXCEPT + maybe(test + maybe(AS + NAME))
try_stmt = (TRY + COLON + suite + choice([
    one_plus(except_clause + COLON + suite) +
    maybe(ELSE + COLON + suite) +
    maybe(FINALLY + COLON + suite),
    FINALLY + COLON + suite
]))
with_item = test + maybe(AS + expr)
with_stmt = WITH + sep_by(with_item) + COLON + suite

## FUNCTIONS
### Arguments
argument = choice([
    test + ASSIGN + test,
    SSTAR + test,
    STAR + test,
    test + maybe(comp_for)
])
arglist = sep_by(argument)

### Definitions
vfpdef = NAME
vfpdef_eq = vfpdef + maybe(ASSIGN + test)
tfpdef = NAME + maybe(COLON + test)

_kwargs = SSTAR + vfpdef + maybe(COMMA)
_tkwargs = SSTAR + tfpdef + maybe(COMMA)

varargslist = choice([
    # Normal and keyword args
    sep_by(vfpdef_eq, trailing=False) +
    maybe(COMMA + maybe(choice([
        STAR + maybe(vfpdef) + many(COMMA + vfpdef_eq) + maybe(
            COMMA + maybe(_kwargs)),
        _kwargs
    ]))),
    STAR + maybe(vfpdef) + many(COMMA + vfpdef_eq) + maybe(
        COMMA + maybe(_kwargs)),
    _kwargs
])

typedargslist = (
    # Normal and keyword args
    (tfpdef + maybe(ASSIGN + test) + many(
        COMMA + tfpdef + maybe(ASSIGN + test)) +
     maybe(COMMA + maybe(
         (STAR + maybe(tfpdef) + many(
             COMMA + tfpdef + maybe(ASSIGN + test)) + maybe(
             COMMA + maybe(_tkwargs))) |
         _tkwargs
     ))) |
    (STAR + maybe(tfpdef) + many(
        COMMA + tfpdef + maybe(ASSIGN + test)) + maybe(
        COMMA + maybe(_tkwargs))) |
    _tkwargs
)

parameters = between(typedargslist, empty=True)
funcdef = (
    DEF + NAME + parameters + maybe(TO + test) +
    try_(COLON, 'missing colon after parameters in function definition') +
    suite
)
async_funcdef = ASYNC + funcdef
async_stmt = ASYNC + (funcdef | with_stmt | for_stmt)

lambdef = LAMBDA + maybe(varargslist) + COLON + test
lambdef_nocond = LAMBDA + maybe(varargslist) + COLON + test_nocond

classdef = CLASS + NAME + maybe(between(arglist, empty=True)) + COLON + suite

decorator = op_('@') + dotted_name + maybe(
    between(arglist, empty=True)) + NEWLINE
decorators = one_plus(decorator)
decorated = decorators + (classdef | funcdef | async_funcdef)

# High-level structure
small_stmt = choice([
    expr_stmt, del_stmt, pass_stmt, flow_stmt, import_stmt,
    global_stmt, nonlocal_stmt, assert_stmt])
# Removed newline for simple_stmt here
simple_stmt = sep_by(small_stmt, SEMI) + maybe(NEWLINE)
compound_stmt = choice([
    if_stmt, while_stmt, for_stmt, try_stmt, with_stmt,
    funcdef, classdef, decorated, async_stmt])
stmt = with_forward_decls(lambda: (simple_stmt | compound_stmt | COMMENT))

file_input = many(NEWLINE | stmt | (COMMENT + NEWLINE)) + ENDMARKER


def parse_file(filename):
    with open(filename) as f:
        tokens = [t for t in generate_tokens(f.readline)
                  if t.type != tokenize.COMMENT and t.type != tokenize.NL]
        try:
            file_input.parse(tokens)
        except CustomParseError as err:
            token = tokens[err.orig_error.state.pos]
            lineno = token.start[0]
            print('Syntax error at line {}. Details:'.format(lineno))
            print('  ' + err.msg)
