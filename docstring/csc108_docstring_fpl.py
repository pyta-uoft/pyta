from funcparserlib.parser import a, forward_decl, maybe, finished, many, skip, oneplus, some, _Tuple


# Precondition: 's' is a string with at least one character
def a_str(s):
    p_out = a(s[0])
    for i in range(1, len(s)):
        p_out += a(s[i])
    return (p_out >> to_str)

def skip_str(s):
    return skip(a_str(s))

def to_str(s):
    return ''.join(s)

# Precondition: args length is >= 1
def inject_whitespace(*args):
    if len(args) == 1:
        return args[0]
    out = args[0]
    for i in range(1, len(args) - 1):
        out += ws + args[i]
    return out + ws + args[-1]

def parse_docstring(docstr):
    return docstring.parse(docstr)

element = forward_decl()
elements = forward_decl()
ws = skip(many(a(' ') | a('\t')))
anystr = oneplus(some(str.isalpha)) >> to_str
a_list = inject_whitespace(a_str('list'), skip_str('of'), element)
a_set = inject_whitespace(a_str('set'), skip_str('of'), element)
a_dict = inject_whitespace(a_str('dict'), skip_str('of'), a('{'), element, a(','), element, a('}'))
a_tuple = inject_whitespace(a_str('tuple'), skip_str('of'), a('('), elements, a(')'))
element.define(a_list | a_set | a_tuple | a_dict | anystr)
elements.define(element + many(ws + a(',') + ws + element))
arg_signature = inject_whitespace(a('('), a(')')) | inject_whitespace(a('('), elements, a(')'))
docstring = inject_whitespace(arg_signature, a_str('->'), element, skip(finished))

# =============================

def flatten(L):
    A = []
    for x in L:
        flatten_rec(x, A)
    return A

def flatten_rec(x, A):
    if isinstance(x, str):
        A.append(x)
    else:
        for y in x:
            flatten_rec(y, A)

def print_nested(L, indent=0):
    indentation = '\t' * indent
    if isinstance(L, str):
        print('%s%s' % (indentation, L))
    else:
        for x in L:
            print_nested(x, indent + 1)
    
# =============================
        
res = parse_docstring('(int, bool, tuple of (Hi, None)) -> bool')
print(res)
#print(flatten(res))
#print_nested(res)
