import typing
from funcparserlib.parser import a, forward_decl, finished, many, maybe, skip, oneplus, some
from tokenize import generate_tokens
from io import StringIO


def a_str(s):
    return some(lambda x: x.string == s)


def skip_str(s):
    return skip(some(lambda x: x.string == s))


def combine_elements_to_list(data):
    output_list = [x for x in data[0]]
    output_list.append(data[-1])
    return output_list


def compile_list_type(data):
    return typing.List[data[1]]


def compile_set_type(data):
    return typing.Set[data[1]]


def compile_dict_type(data):
    return typing.Dict[data[1], data[2]]


# Despite the data being a list of class types, Tuple[...] will not accept a
# list, but will accept a tuple() that was converted from a list.
def compile_tuple_type(data):
    return typing.Tuple[tuple(data[-1])]


def to_simple_type(token):
    s = token.string
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


# -----------------------------------------------------------------------------

element = forward_decl()
elements = forward_decl()

skip_of = skip_str('of')
any_class = some(lambda x: True) >> to_simple_type

set_parser = (a_str('set') + skip_of + element) >> compile_set_type

list_parser = (a_str('list') + skip_of + element) >> compile_list_type

dict_parser = (a_str('dict') + skip_of + skip_str('{') + element + skip_str(',') + element + skip_str('}')) >> \
              compile_dict_type

tuple_parser = (a_str('tuple') + skip_of + skip_str('(') + (elements >> combine_elements_to_list) + skip_str(')')) >> \
               compile_tuple_type

element.define(set_parser | list_parser | dict_parser | tuple_parser | any_class)
elements.define(maybe(many(element + skip_str(','))) + element)

# TODO - Need to strip a [] leftover if there's one element at the beginning.
docstring_parser = skip_str('(') + elements + skip_str(')') + skip_str('->') + element

# -----------------------------------------------------------------------------

# non_right_arrow = some(lambda x: x != '>')
# single_arrow = a_str('>') + non_right_arrow
# double_arrow = a_str('>>') + non_right_arrow
# docstring_description = oneplus(non_right_arrow | single_arrow | double_arrow) >> to_str

# docstring_doctest = a_str('>>>') + (oneplus(some(is_valid_char)) >> to_str)

# -----------------------------------------------------------------------------

docstring_raw = '(dict of {SomeFakeClass, tuple of (bool, int, str, NoneType)}, int) -> list of list of SomeClass'
output = list(generate_tokens(StringIO(docstring_raw).readline))
out = docstring_parser.parse(output)
print(out)
