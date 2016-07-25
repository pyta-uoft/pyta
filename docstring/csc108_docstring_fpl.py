from funcparserlib.parser import a, forward_decl, finished, many, maybe, skip, oneplus, some


# Precondition: 's' is a string with at least one character
def a_str(s):
    p_out = a(s[0])
    for i in range(1, len(s)):
        p_out += a(s[i])
    return p_out >> to_str


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


def is_valid_char(c):
    return 32 <= ord(c) <= 127 or c in ['\n', '\t', '\r']


def flatten(list_of_parsed_elements):
    out = []
    rec_flatten(list_of_parsed_elements, out)
    return out


def rec_flatten(list_or_str, out):
    if isinstance(list_or_str, str):
        out.append(list_or_str)
        return
    for x in list_or_str:
        rec_flatten(x, out)


# =====================================

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
arg_signature = inject_whitespace(skip(a('(')), skip(a(')'))) | inject_whitespace(skip(a('(')), elements, skip(a(')')))
docstring_signature = inject_whitespace(arg_signature, a_str('->'), element)

# =====================================

non_right_arrow = some(lambda x: x != '>')
single_arrow = a_str('>') + non_right_arrow
double_arrow = a_str('>>') + non_right_arrow
docstring_description = oneplus(non_right_arrow | single_arrow | double_arrow) >> to_str

# =====================================

docstring_doctest = a_str('>>>') + (oneplus(some(is_valid_char)) >> to_str)

# =====================================

docstring_parser = docstring_signature + docstring_description + docstring_doctest + skip(finished)
docstring_parser_maybe = maybe(docstring_signature) + maybe(docstring_description) + maybe(docstring_doctest) + skip(finished)

# =====================================

# -------------------------------------
# Test a valid docstring
# -------------------------------------

TEST_DOCSTRING_SIGNATURE = '(int, list of bool) -> dict of {int, string}'
TEST_DOCSTRING_DESCRIPTION = 'This is a docstring.\nIt is a great example.'
TEST_DOCSTRING_DOCTEST = """>>> yes(5, [True])\nNone\n>>> func(123)\nOutput"""
TEST_DOCSTRING = TEST_DOCSTRING_SIGNATURE + '\n' + TEST_DOCSTRING_DESCRIPTION + '\n' + TEST_DOCSTRING_DOCTEST

data = docstring_parser.parse(TEST_DOCSTRING)
flat = flatten(data[:-2])
print(flat)

# -------------------------------------
# Test incorrect docstrings
# -------------------------------------

INVALID_DOCSTRING1 = """(int) -> bool\nThere's no doctest with this!"""
data1 = docstring_parser_maybe.parse(INVALID_DOCSTRING1)
print(data1)

INVALID_DOCSTRING2 = """Purely a description..."""
data2 = docstring_parser_maybe.parse(INVALID_DOCSTRING2)
print(data2)

INVALID_DOCSTRING3 = """>>> f('only doctests')\nNone\n>>> f('malformed doctest')"""
data3 = docstring_parser_maybe.parse(INVALID_DOCSTRING3)
print(data3)
