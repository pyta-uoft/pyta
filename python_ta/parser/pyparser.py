from funcparserlib.parser import finished, many, maybe, skip, some, a, with_forward_decls, forward_decl
from tokenize import generate_tokens
from io import StringIO
import token
import operator
import functools
import typing


class Token(object):
    def __init__(self, code, value, start=(0, 0), stop=(0, 0), line=''):
        self.code = code
        self.value = value
        self.start = start
        self.stop = stop
        self.line = line

    @property
    def type(self):
        return token.tok_name[self.code]

    def __unicode__(self):
        pos = '-'.join('%d,%d' % x for x in [self.start, self.stop])
        return "%s %s '%s'" % (pos, self.type, self.value)

    def __repr__(self):
        return 'Token(%r, %r, %r, %r, %r)' % (
            self.code, self.value, self.start, self.stop, self.line)

    def __eq__(self, other):
        return (self.code, self.value) == (other.code, other.value)


# lexer function
def tokenize(s):
    return list(Token(*t)
        for t in generate_tokens(StringIO(s).readline)
                    if t[0] not in [token.NEWLINE])


def parse(tokens):
    const = lambda x: lambda _: x
    unarg = lambda f: lambda x: f(*x)

     # Semantic actions and auxiliary functions
    tokval = lambda tok: tok.value
    makeop = lambda s, f: op(s) >> const(f)

    def eval_expr(z, list):
        'float, [((float, float -> float), float)] -> float'
        return functools.reduce(lambda s, f_x: f_x[0](s, f_x[1]), list, z)
    
    eval = unarg(eval_expr)

    @unarg
    def make_list(first, rest):
        if len(rest) == 0:
            return [first]
        else:
            items = list(rest)
            items.insert(0, first)
            return items
    
    
    def make_maybe_empty_list(arg):
        if arg is None:
            return []
        else:
            return make_list(arg)
    
    def make_number(s):
        try:
            return int(s)
        except ValueError:
            return float(s)
    
    def make_string(s):
        return str(s)
        
    number = (
        some(lambda tok: tok.code == token.NUMBER)
        >> tokval
        >> make_number)
    
    string = (
     some(lambda tok: tok.code == token.STRING)
     >> tokval
     >> (lambda s: s[1:-1]))

    def skip_str(s):
        return skip(some(lambda x: x.string == s))
    
    name = (
        some(lambda tok: tok.code == token.NAME)
        >> tokval)
    
    await = (
        some(lambda tok: tok.code == token.AWAIT)
        >> tokval)    
    
    star = (
        some(lambda tok: tok.code == token.STAR)
        >> tokval)
    
    
    # operator
    op = lambda s: a(Token(token.OP, s)) >> tokval
    op_ = lambda s: skip(op(s))

    # Means of composition
    @with_forward_decls
    def primary1():
        return number | (op_('(') + expr + op_(')'))
    
    @with_forward_decls
    def primary2():
        return  (op_('(') + expr + op_(')'))

    rawname = (some(lambda tok: tok.code == token.NAME) >> tokval)
    
    kw = lambda s: skip(a(Token(token.NAME, s)))
    
    newline = skip(a(Token(token.NEWLINE, '\n')))
    indent = skip(a(Token(token.INDENT, '    ')))
    dedent = skip(a(Token(token.DEDENT, '')))
    
    comma = op_(',')
    semicolon = op_(';')
    dot = op_('.')
    colon = op_(':')
    dbl_quote = op_('"')
    assign = colon + op_('=')
    
    openparen = op_('(')
    closeparen = op_(')')
    inparens = lambda s: openparen + s + closeparen
    
    opencurlyparen = op_('{')
    closecurlyparen = op_('}')
    incurlyparens = lambda s: opencurlyparen + s + closecurlyparen
    
    openbracket = op_('[')
    closebracket = op_(']')
    inbrackets = lambda s: openbracket + s + closebracket
    
    listof = lambda s: (s + many(comma + s)) >> make_list
    
    maybe_empty_listof = lambda s: maybe(s + many(comma + s)) >> make_maybe_empty_list 
    
    
    add = makeop('+', operator.add)
    sub = makeop('-', operator.sub)
    mul = makeop('*', operator.mul)
    div = makeop('/', operator.__truediv__)
    pow = makeop('**', operator.pow)
    mod = makeop('%', operator.mod)
    floor_div = makeop('//', operator.floordiv)
    
    # comp_op
    eq = makeop('==', operator.eq)
    lt = makeop('<', operator.lt)
    le = makeop('<=', operator.le)
    ne1 = makeop('!=', operator.ne)
    ne2 = makeop("<>", operator.ne)
    ge = makeop('>=', operator.ge)
    gt = makeop('>',operator.gt)
    cin = makeop('in', operator.contains)
    cis = makeop('is',operator.is_)
    cisnot = makeop('is not', operator.is_not)
    
    # augassign
    an = makeop('+=', operator.iadd)
    sn = makeop('-=', operator.isub)
    muln = makeop('*=', operator.imul)
    dn = makeop('/=', operator.itruediv)
    fdn = makeop('//=', operator.ifloordiv)
    pn = makeop('**=', operator.ipow)
    mon = makeop('%=',operator.imod)
    irightshift = makeop('>>=', operator.irshift)
    ileftshift = makeop('<<=', operator.ilshift)
    ior = makeop('|=', operator.ior)
    ixor = makeop('^=', operator.ixor)
    

    no = makeop('!', operator.not_)
    band = makeop('&', operator.and_)
    bxor = makeop('^', operator.xor)
    inv = makeop('~', operator.invert)
    bor = makeop('|', operator.or_)
    leftshift = makeop('<<', operator.lshift)
    rightshift = makeop('>>', operator.rshift)  
    
    mul_op = mul | div | mod | floor_div
    add_op = add | sub
    shift = leftshift | rightshift
    com_op = lt | gt | le | ge
    eq_op = eq | ne1 | ne2
    asslst = an | sn | muln | dn | fdn | pn | fdn | mon
    is_op = cis | cisnot
    # TODO
    
    # atom: ('(' [yield_expr|testlist_comp] ')' |
    #    '[' [testlist_comp] ']' |
    #    '{' [dictorsetmaker] '}' |
    #    NAME | NUMBER | STRING+ | '...' | 'None' | 'True' | 'False')
    # not used in grammar, but may appear in "node" passed from Parser to Compiler
    # encoding_decl: NAME
    # 
    # yield_expr: 'yield' [yield_arg]
    # yield_arg: 'from' test | testlist
    
    #TODO left: '@=' | '&='
    augassign = an | sn | muln | dn | mon | fdn | irightshift | ileftshift \
                | ior | ixor
    
    #TODO can not find 'not in' function?
    comp_op = lt | gt | le | ge | eq | ne1 | ne2 | cin | cis | cisnot

    #TODO # power: atom_expr ['**' factor]
    #TODO what about factor and power
    #
    power = (pow)
    factor_c = add | sub | inv
    # !
    factor = many(factor_c) | power
    #TODO no "@"
    term_c = mul | div | floor_div | mod
    term = factor + many(term_c + factor)
    add_sub = add | sub
    arith_expr = term + many(add_sub + term)
    shift = leftshift | rightshift
    shift_expr = arith_expr + many(shift + arith_expr)
    and_expr = shift_expr + many(band + shift_expr)
    xor_expr = and_expr + many(bxor + and_expr)
    expr = xor_expr + many(bor + xor_expr)
    star_expr = expr + many(star + expr)
    #TODO what is the difference between {} []
    # atom: ('(' [yield_expr|testlist_comp] ')' |
    #    '[' [testlist_comp] ']' |
    #    '{' [dictorsetmaker] '}' |
    #    NAME | NUMBER | STRING+ | '...' | 'None' | 'True' | 'False')
    atom = number | str | name
    
    
    
    
    
    
    
    # Means of composition
    @with_forward_decls
    def primary():
        return number | (op_('(') + expr + op_(')'))
    f1 = primary + many(pow + primary) >> eval
    f2 = f1 + many(inv + f1) >> eval
    f3 = f2 + many(mul_op + f2) >> eval
    f4 = f3 + many(add_op + f3) >> eval
    f5 = f4 + many(shift + f4) >> eval
    f6 = f5 + many(band + f5) >> eval
    f7 = f6 + many(bor + f6) >> eval
    f8 = f7 + many(com_op + f7) >> eval
    f9 = f8 + many(eq_op + f8) >> eval
    f10 = f9 + many(asslst + f9) >> eval
    f11 = f10 + many(eq_op + f10) >> eval
    f12 = f11 + many(asslst + f11) >> eval
    f13 = f12 + many(is_op + f12) >> eval
    f14 = f13 + many(cin + f13) >> eval
    expr = f14 + many(no + f14) >> eval
    
    
    # Toplevel parsers
    endmark = a(Token(token.ENDMARKER, ''))
    end = skip(endmark + finished)
    toplevel = maybe(expr) + end

    return toplevel.parse(tokens)

if __name__ == "__main__":
    print(parse(tokenize('1<2')))