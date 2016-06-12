"""
BNF:
    basetype = ( "int" | "float" | "bool" | "str" | "obj" | "NoneType" )
    tuple = "(" element [ "," element ]+ ")"
    dict = "{" element [ "," element ]+ "}"
    collection = ( "list" "of" element | "set" "of" element | "tuple" "of" tuple | "dict" "of" dict )
    element = ( basetype | collection )
    elements = element [ "," element ]+
    type_contract = "(" elements ")" "->" elements
    
NOTE: Whitespace doesn't matter for symbols, but does for 'collection' elements.
"""

_VALID_TOKENS = [',', '(', ')', '[', ']', '{', '}']
_COLLECTION_TYPES = ['list', 'set', 'tuple', 'dict']
_BASE_TYPES = ['int', 'float', 'bool', 'str', 'obj', 'NoneType']


class NotA108DocstringException(Exception):
    """Indicates a parsing exception (malformed docstring header)."""
    pass


class UnexpectedToken(Exception):
    """Raised when an unexpected character is in the docstring."""
    pass


class DocNode:
    """Represents a node in a tree of nodes which can be analyzed to get the
    parsed elements of a docstring header.
    """
    def __init__(self, node_type=None, val=''):
        self.children = []
        self.node_type = node_type
        self.val = val


def tokenize_docstring(docstr):
    """Tokenizes a docstring into tokens for the parser.
    Accepts a docstring, and returns a list of tokens.
    """
    tokens = []
    current_token = ''
    should_skip = False
    for i in range(len(docstr)):
        if should_skip:
            should_skip = False
            continue
        c = docstr[i]
        if c in _VALID_TOKENS:
            if len(current_token) > 0:
                tokens.append(current_token)
                current_token = ''
            tokens.append(c)
        elif c == '-':
            if i >= len(docstr) - 1:
                raise UnexpectedToken('Expected -> but got docstring end')
            next_c = docstr[i+1]
            if next_c != '>':
                raise UnexpectedToken('Expected -> but got -' + next_c)
            if len(current_token) > 0:
                tokens.append(current_token)
                current_token = ''
            tokens.append('->')
            should_skip = True  # TODO - need to advance iterator here by one extra...
        elif c.isalpha():
            current_token += c
        elif c == ' ' or c == '\t':
            if len(current_token) > 0:
                tokens.append(current_token)
                current_token = ''
        else:
            raise UnexpectedToken('Unexpected docstring character: ' + c)
    # We will likely have a leftover unprocessed token at the end, handle it.
    if len(current_token) > 0:
        tokens.append(current_token)
    return tokens


class DocstringParser:
    """Used in parsing the recursive nature of a docstring.
    Upon calling the constructor, the object will begin processing the docstring
    line immediately, so upon returning there will either be an exception due to
    a malformed string, or the developed.
    Can throw either NotA108DocstringException or UnexpectedToken from the
    constructor."""
    def __init__(self, entire_docstring):
        docstring_header = trim_docstring_down_to_type_contract(entire_docstring)
        self.tokens = tokenize_docstring(docstring_header)
        self.markers = []
        self.token_index = 0
        self.args_node = DocNode()
        self.return_node = DocNode()
        self.root_doc_node = DocNode()
        self.root_doc_node.children = [self.args_node, self.return_node]
        self.parse_type_contract()

    def parse_type_contract(self):
        self.consume_token_type_or_error('(')
        self.parse_elements_until_right_paren()
        self.consume_token_type_or_error(')')
        self.consume_token_type_or_error('->')
        self.parse_elements_until_end()
        
    def parse_elements_until_right_paren(self):
        while self.tokens[self.token_index] != ')':
            # TODO - Start a new element
            self.parse_element()
            while self.tokens[self.token_index] == ',':
                self.consume_token_type_or_error(',')
                # TODO - Start a new element
                self.parse_element()

    def parse_elements_until_end(self):
        while self.token_index < len(self.tokens):
            # TODO - Start a new element
            self.parse_element()
        
    def parse_element(self):
        if not self.parse_collection():
            if not self.parse_base_type():
                raise NotA108DocstringException()

    def parse_collection(self):
        if self.tokens[self.token_index] == 'list':
            # TODO - is a list
            self.token_index += 1
            self.consume_token_type_or_error('of')
            self.parse_element()
            return True
        elif self.tokens[self.token_index] == 'set':
            # TODO - is a set
            self.token_index += 1
            self.consume_token_type_or_error('of')
            self.parse_element()
            return True
        elif self.tokens[self.token_index] == 'tuple':
            # TODO - is a tuple
            self.token_index += 1
            self.consume_token_type_or_error('of')
            self.parse_tuple()
            return True
        elif self.tokens[self.token_index] == 'dict':
            # TODO - is a dict
            self.token_index += 1
            self.consume_token_type_or_error('of')
            self.parse_dict()
            return True
        return False

    def parse_dict(self):
        self.consume_token_type_or_error('{')
        self.parse_element()
        self.consume_token_type_or_error(',')
        self.parse_element()
        self.consume_token_type_or_error('}')

    def parse_tuple(self):
        self.consume_token_type_or_error('(')
        self.parse_element()
        while self.tokens[self.token_index] == ',':
            self.consume_token_type_or_error(',')
            self.parse_element()
        self.consume_token_type_or_error(')')

    def parse_base_type(self):
        if self.tokens[self.token_index] not in _BASE_TYPES:
            return False
        # TODO - Convert to type and store in DocNode
        return True

    def consume_token_type_or_error(self, token_str):
        if self.token_index >= len(self.tokens):
            raise NotA108DocstringException('Expected "%s", terminated early' % token_str)
        token = self.tokens[self.token_index]
        if token != token_str:
            raise NotA108DocstringException('Expected "%s", got "%s" instead' % (token_str, token))
        self.token_index += 1

    
def trim_docstring_down_to_type_contract(full_docstring):
    """Extracts the line we want (the type contract) from the entire docstring.
    This assumes there always will be a docstring, whereby it will read the top
    line and continue reading until it hits an empty line, of which it will then
    assume the docstring header to be done. This allows for a docstring to be
    multiple lines, like:
        (int, set of list of tuple of(int, str), obj)
            ->
                tuple of (int, int)
    This is needed since PEP-8 being enforced in CSC108 means the possibility of
    the docstring being greater than 80 characters, and it must be supported if
    its too long.
    This function will properly extract the string and compress it into a single
    string with all newlines/improper spacing removed.
    Note: This does not check for correctness of the docstring header contract,
    its job is only to extract the docstring, and let the parser error out if
    the type contract is malformed.
    """
    lines = full_docstring.split('\n')  # TODO - Support \r\n too.
    merged_docstring = ''
    for line in lines:
        stripped_line = line.strip()
        if len(stripped_line) <= 0:
            break
        # Lack of whitespace between lines could cause problems, so we will
        # assume there is supposed to be a space to replace the new line.
        # Since the parser will skip any extra space, this is safe to do.
        merged_docstring += stripped_line + ' '
    return merged_docstring[:-1]  # Trim last space (TODO - do this better)


def parse_csc108_docstring(full_docstring):
    """Takes the header line of a docstring which is supposed to be the
    docstring, and parses it. If parsing fails, a NotA108DocstringException
    is raised.
    Returns two nodes as a tuple: (Args tree DocNode, result tree DocNode).
    """
    line = trim_docstring_down_to_type_contract(full_docstring)
    parser = DocstringParser(line)
    return parser.args_node, parser.return_node
