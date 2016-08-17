import typing
import re
from funcparserlib.parser import forward_decl, finished, many, maybe, skip, oneplus, some
from tokenize import generate_tokens
from io import StringIO


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
    return typing.Tuple[tuple(data[1])]


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
elements.define((many(element + skip_str(',')) + element) >>
                (lambda x: x[0] + [x[1]]))
type_contract_parser = skip_str('(') + maybe(elements) + skip_str(')') + skip_str('->') + element

docstring_description = many(some(lambda token: '>>>' not in token.line)) >> (lambda tokens: ' '.join(token.string for token in tokens))

docstring_doctest = many(some(lambda token: True)) >> (lambda tokens: ' '.join(token.string for token in tokens))

entire_docstring = maybe(type_contract_parser) + docstring_description +\
                   docstring_doctest + finished


def parse_csc108_docstring(docstring):
    """Reads a docstring in the CSC108 format and extracts the argument types.
    @param str docstring: The docstring to read.
    @return: A parsed output of the docstring.
    """
    output = list(generate_tokens(StringIO(docstring.strip()).readline))
    return entire_docstring.parse(output)[:4]


if __name__ == '__main__':
    # Sample test
    r = parse_csc108_docstring("""
      (tuple of (int, int), str) -> list of int

      This function does something pretty cool

      >>> f(1)
      10
      >>> f(2)
      42
      >>> f(3)
      45
      """)

    print('Function inputs', r[0])
    print('Function output', r[1])
    print('Description', r[2])
    print('Doctests', r[3])
