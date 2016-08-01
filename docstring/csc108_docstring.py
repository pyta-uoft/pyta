from funcparserlib.parser import a, forward_decl, finished, many, maybe, skip, oneplus, some
from typing import *


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
    recursively_flatten(list_of_parsed_elements, out)
    return out


def recursively_flatten(list_or_str, out):
    if isinstance(list_or_str, str):
        out.append(list_or_str)
        return
    for x in list_or_str:
        recursively_flatten(x, out)


def replace_spaces_after_newline(combined_line):
    lines = combined_line.split('\n')
    output_lines = [line.strip() for line in lines]
    return '\n'.join(output_lines)


# The parser gives us back a modified Tuple class, and if there is only one
# argument then theres an additonal list that trails the '->' which is not
# needed. This function will convert the Tuple to a List and extract this empty
# list if it exists.
def convert_to_list_and_extract_junk(flattened_data):
    output_list = list(flattened_data)
    # Since we are modifying the output_list, we can't iterate over it at the
    # same time as we potentially delete things from it, so we use the original
    # data for comparing.
    for i in range(len(flattened_data)):
        if flattened_data[i] == '->' and i > 0 and flattened_data[i - 1] == []:
            del output_list[i - 1]
            break
    return output_list


# Method signature
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

# Method description.
non_right_arrow = some(lambda x: x != '>')
single_arrow = a_str('>') + non_right_arrow
double_arrow = a_str('>>') + non_right_arrow
docstring_description = oneplus(non_right_arrow | single_arrow | double_arrow) >> to_str

# Method docstring.
docstring_doctest = a_str('>>>') + (oneplus(some(is_valid_char)) >> to_str)

# The final parser.
docstring_parser_maybe = maybe(docstring_signature) + maybe(docstring_description) + maybe(docstring_doctest) + skip(finished)


class ParsedDocstring108:
    """Reads in a CSC108 docstring and parses it. If it is malformed, then an
    exception will be thrown. Otherwise, all the data will be populated and
    accessible through the signature, description, and doctests field.
    The exception is only thrown if the docstring format is incorrect.
    The signature field will contain Typing elements, though any classes that
    are created by the user will be a String representation of the class name
    (which may be a _ForwardDecl type). This is None if not found.
    The description is a string. This is None if not found.
    The doctests is a string of doctests. This is None if not found.
    """
    def __init__(self, docstring):
        # The signature needs special handling.
        parsed_data = docstring_parser_maybe.parse(docstring)
        if not parsed_data[0]:
            self.signature_args_list = None
            self.signature_return_type = None
        else:
            flattened_data = flatten(parsed_data[:-2])
            clean_data = convert_to_list_and_extract_junk(flattened_data)
            self.convert_signature_to_typing(clean_data)
        # The description tends to have junk around it in a proper docstring.
        self.description = parsed_data[-2]
        if self.description:
            self.description = replace_spaces_after_newline(self.description)
            self.description = self.description.strip('\n')
        # Due to how funcparserlib handles things, it returns a tuple of two
        # strings that can be merged, assuming it's present.
        self.doctests = parsed_data[-1]
        if self.doctests:
            self.doctests = self.doctests[0] + self.doctests[1]
            self.doctests = replace_spaces_after_newline(self.doctests)
            self.doctests = self.doctests.strip('\n')

    def convert_signature_to_typing(self, data):
        if not data:
            return
        # Keep reading elements until the arrow.
        self.signature_args_list = []
        while (data[0] != '->'):
            element = ParsedDocstring108.extract_element(data)
            self.signature_args_list.append(element)
            if data[0] == ',':
                data.pop(0)
        self.signature_return_type = None
        data.pop(0)  # Remove the arrow.
        # If anything is left, read the last element.
        if len(data) > 0:
            self.signature_return_type = ParsedDocstring108.extract_element(data)

    @staticmethod
    def extract_element(data):
        first_data_element = data.pop(0)
        if first_data_element == 'int':
            return int
        elif first_data_element == 'str':
            return str
        elif first_data_element == 'float':
            return float
        elif first_data_element == 'bool':
            return bool
        elif first_data_element in ['obj', 'object']:
            return typing.Any
        elif first_data_element in ['None', 'NoneType']:
            return type(None)
        elif first_data_element == 'list':
            inner_type = ParsedDocstring108.extract_element(data)
            return List[inner_type]
        elif first_data_element == 'set':
            inner_type = ParsedDocstring108.extract_element(data)
            return Set[inner_type]
        elif first_data_element == 'dict':
            data.pop(0)  # Remove { symbol.
            key_type = ParsedDocstring108.extract_element(data)
            data.pop(0)  # Remove comma.
            value_type = ParsedDocstring108.extract_element(data)
            data.pop(0)  # Remove } symbol.
            return Dict[key_type, value_type]
        elif first_data_element == 'tuple':
            data.pop(0)  # Remove leading bracket.
            list_types = []
            while data[0] != ')':
                inner_type = ParsedDocstring108.extract_element(data)
                list_types.append(inner_type)
                if data[0] == ',':
                    data.pop(0)  # Remove comma.
            data.pop(0)  # Remove ending bracket.
            return Tuple[list_types]
        return first_data_element  # Assume at this point it must be a class.

    def __str__(self):
        return '%s -> %s, %s, %s' % (self.signature_args_list, self.signature_return_type,
                                     self.description, self.doctests)
