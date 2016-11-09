from funcparserlib import finished, many, maybe, skip, some, a, with_forward_decls, forward_decl
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
    
    def make_number(s):
        try:
            return int(s)
        except ValueError:
            return float(s)
    
    def to_simple_type(s):
        try:
            if s == 'int':
                return int
            elif s == 'str':
                return str
            elif s == 'float':
                return float
            elif s == 'bool':
                return bool
            elif s in ['obj', 'object']:
                return typing.Any
            elif s in ['None', 'NoneType']:
                return type(None)
            return s
        except ValueError:
            raise
        
    number = (
        some(lambda tok: tok.code == token.NUMBER)
        >> tokval
        >> make_number)
    
    str = (
        some(lambda tok: tok.code == token.STRING)
        >> tokval
        >> to_simple_type)
    
    # operator
    op = lambda s: a(Token(token.OP, s)) >> tokval
    op_ = lambda s: skip(op(s))

    add = makeop('+', operator.add)
    sub = makeop('-', operator.sub)
    mul = makeop('*', operator.mul)
    div = makeop('/', operator.__truediv__)
    pow = makeop('**', operator.pow)
    mod = makeop('%', operator.mod)
    floor_div = makeop('//', operator.floordiv)
    
    # comparison operator
    eq = makeop('==', operator.eq)
    lt = makeop('<', operator.lt)
    le = makeop('<=', operator.le)
    ne = makeop('!=', operator.ne)
    ge = makeop('>=', operator.ge)
    gt = makeop('>',operator.gt)
    cin = makeop('in', operator.contains)
    cis = makeop('is',operator.is_)
    cisnot = makeop('is not', operator.is_not)
        
    # logical operator
    no = makeop('!', operator.not_)

    # assignment operator
    an = makeop('+=', operator.iadd)
    sn = makeop('-=', operator.isub)
    muln = makeop('*=', operator.imul)
    dn = makeop('/=', operator.itruediv)
    fdn = makeop('//=', operator.ifloordiv)
    pn = makeop('**=', operator.ipow)
    mon = makeop('%=',operator.imod)
    
    
    # bitwise operator
    band = makeop('&', operator.and_)
    bxor = makeop('^', operator.xor)
    inv = makeop('~', operator.invert)
    bor = makeop('|', operator.or_)
    leftshift = makeop('<<', operator.lshift)
    rightshift = makeop('>>', operator.rshift)  
    
    # Operator	Description Precedence
    # **	Exponentiation (raise to the power)
    # ~ + -	Complement, unary plus and minus (method names for the last two are +@ and -@)
    # * / % //	Multiply, divide, modulo and floor division
    # + -	Addition and subtraction
    # >> <<	Right and left bitwise shift
    # &	Bitwise 'AND'	
    # ^ |	Bitwise exclusive `OR' and regular `OR'
    # <= < > >=	Comparison operators
    # <> == !=	Equality operators
    # = %= /= //= -= += *= **=	Assignment operators
    # is is not	Identity operators
    # in not in	Membership operators
    # not or and	Logical operators
    
    mul_op = mul | div | mod | floor_div
    add_op = add | sub
    shift = leftshift | rightshift
    com_op = lt | gt | le | ge
    eq_op = eq | ne
    asslst = an | sn | muln | dn | fdn | pn | fdn | mon
    is_op = cis | cisnot
    
    # more operators
    #TODO
    

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
    print(parse(tokenize('3 //= 3')))
    print(parse(tokenize('3 += 3')))
    print(parse(tokenize('(3 - 3) * 3 + (3 * 3)')))
    print(parse(tokenize('((3 - 1) * 3) + (3 * 3)')))
    print(parse(tokenize('2 * 32 ** 1')) == 64)
    print(parse(tokenize('2 ** 32 - 1')) == 4294967295)