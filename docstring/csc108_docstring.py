import typing
import re
from funcparserlib.parser import forward_decl, finished, many, maybe, skip, oneplus, some
from tokenize import generate_tokens
from io import StringIO


def flatten(nested_list):
    output_list = []
    recursively_flatten(nested_list, output_list)
    return output_list


def recursively_flatten(item, output_list):
    if not isinstance(item, list) and not isinstance(item, tuple):
        output_list.append(item)
        return
    for x in item:
        recursively_flatten(x, output_list)


def a_str(s):
    return some(lambda x: x.string == s)


def skip_str(s):
    return skip(some(lambda x: x.string == s))


def combine_elements_to_list(data):
    if len(data) <= 1:
        return data
    output_list = [x for x in data[0]]
    output_list.append(data[-1])
    return output_list


def compile_list_type(data):
    return typing.List[data[1]]


def compile_set_type(data):
    return typing.Set[data[1]]


def compile_dict_type(data):
    return typing.Dict[data[1], data[2]]


def compile_tuple_type(data):
    flat_data = flatten(data[1:])
    return typing.Tuple[tuple(flat_data)]


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


element = forward_decl()
elements = forward_decl()
skip_of = skip_str('of')
any_class = some(lambda x: re.match('[a-zA-Z0-9_]+', x.string)) >> to_simple_type
set_parser = (a_str('set') + skip_of + element) >> compile_set_type
list_parser = (a_str('list') + skip_of + element) >> compile_list_type
dict_parser = (a_str('dict') + skip_of + skip_str('{') + element + skip_str(',') + element + skip_str('}')) >> \
              compile_dict_type
tuple_parser = (a_str('tuple') + skip_of + skip_str('(') + elements + skip_str(')')) >> compile_tuple_type
element.define(set_parser | list_parser | dict_parser | tuple_parser | any_class)
elements.define(maybe(many(element + skip_str(','))) + element)
docstring_parser = skip_str('(') + maybe(elements) + skip_str(')') + skip_str('->') + element

non_right_arrow = some(lambda x: x != '>')
single_arrow = a_str('>') + non_right_arrow
double_arrow = a_str('>>') + non_right_arrow
docstring_description = oneplus(non_right_arrow | single_arrow | double_arrow) >> to_str

docstring_doctest = a_str('>>>') + (oneplus(some(is_valid_char)) >> to_str)

entire_docstring = maybe(docstring_parser) + maybe(docstring_description) + maybe(docstring_doctest) + finished


def parse_csc108_docstring(docstring):
    """Reads a docstring in the CSC108 format and extracts the argument types.
    @param str docstring: The docstring to read.
    @return: A parsed output of the docstring as a argument -> type list.
    """
    output = list(generate_tokens(StringIO(docstring.strip()).readline))
    out = docstring_parser.parse(output)
    out = [x for x in out if x is not None]
    output_list = combine_elements_to_list(out[:-1])
    output_list.append(out[-1])
    return output_list
