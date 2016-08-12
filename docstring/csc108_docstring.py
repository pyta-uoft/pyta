"""
BNF for csc108 docstring:
    set = "set" "of" element
    dict = "dict" "of" "{" element "," element "}"
    tuple = "tuple" "of" "(" elements ")"
    list = "list" "of" element
    collection = list | tuple | dict | set
    element = collection | <ANY_STRING>
    elements = element ("," element)*
    typeContract = "(" elements ")" "->" element
"""

_VALID_TOKENS = [',', '(', ')', '[', ']', '{', '}']
_COLLECTION_TYPES = ['list', 'set', 'tuple', 'dict']


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
    def __init__(self, node_type=None):
        self.children = []
        self.node_type = node_type


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
        """Creates an object that will have the entire parsed docstring set in
        the args_node and return_node DocNode objects.
        entire_docstring: The docstring to parse, which does not have to be a
        single line.
        Raises UnexpectedToken if the tokenizer detects an invalid token.
        Raises NotA108DocstringException if the docstring is not in a form
        that can be parsed properly (implies malformed docstring).
        """
        docstring_header = trim_docstring_down_to_type_contract(entire_docstring)
        self.args_node = DocNode()
        self.return_node = DocNode()
        self.node_stack = [self.args_node]
        self.tokens = tokenize_docstring(docstring_header)
        self.token_index = 0
        try:
            self.parse_type_contract()
        except IndexError:
            raise NotA108DocstringException

    def parse_type_contract(self):
        """Parses the entire type contract, of which it will have raised an
        exception or fully parsed the docstring.
        """
        self.consume_token_type_or_error('(')
        self.parse_elements_until_right_paren()
        self.consume_token_type_or_error(')')
        self.consume_token_type_or_error('->')
        self.parse_elements_until_end()
        
    def parse_elements_until_right_paren(self):
        """Parses the docstring data to the left of the arrow and inside the
        brackets. Raises an exception if it is not a proper docstring.
        """
        if self.get_current_token() == ')':
            return
        self.parse_element()
        while self.get_current_token() == ',':
            self.consume_token_type_or_error(',')
            self.parse_element()

    def parse_elements_until_end(self):
        """Parses the results side of the docstring. Raises an exception if it
        is not a proper docstring.
        """
        self.node_stack = [self.return_node]
        self.parse_element()
        self.raise_if_not_all_tokens_consumed()
        
    def parse_element(self):
        """Parses an element recursively in a docstring. Raises an exception
        if it is not a proper docstring.
        """
        node_type = self.get_current_token()
        self.advance_to_next_token()
        if node_type in _COLLECTION_TYPES:
            self.consume_token_type_or_error('of')
            if node_type in ['list', 'set']:
                self.parse_list_or_set(node_type)
            elif node_type == 'dict':
                self.parse_dict()
            elif node_type == 'tuple':
                self.parse_tuple()
            else:
                raise NotA108DocstringException('Unexpected collection: ' + node_type)
        else:
            self.add_as_child_node(DocNode(node_type))

    def parse_list_or_set(self, node_type):
        """Parses a list or set. Raises an exception if it is not a proper
        docstring.
        node_type: The node type to be set (should be 'list' or 'set').
        """
        node = DocNode(node_type)
        self.add_as_child_node(node)
        self.push_node_on_stack(node)
        self.parse_element()
        self.pop_node_stack()

    def parse_dict(self):
        """Parses a dictionary element recursively. Raises an exception if it
        is not a proper docstring.
        """
        self.consume_token_type_or_error('{')
        node = DocNode('dict')
        self.add_as_child_node(node)
        self.push_then_parse_then_pop(node)
        self.consume_token_type_or_error(',')
        self.push_then_parse_then_pop(node)
        self.consume_token_type_or_error('}')

    def parse_tuple(self):
        """Parses a tuple recursively. Raises an exception if it is not a
        proper docstring.
        """
        self.consume_token_type_or_error('(')
        node = DocNode('tuple')
        self.add_as_child_node(node)
        self.push_then_parse_then_pop(node)
        while self.get_current_token() == ',':
            self.consume_token_type_or_error(',')
            self.push_then_parse_then_pop(node)
        self.consume_token_type_or_error(')')

    def consume_token_type_or_error(self, token_str):
        """Consumes the token that is provided in the argument. If the token
        is not found, then it will throw a NotA108DocstringException. The
        stream will be advanced.
        token_str: The string that should be found on the current token in the
        stream.
        """
        if self.token_index >= len(self.tokens):
            raise NotA108DocstringException('Expected "%s", terminated early' % token_str)
        token = self.get_current_token()
        if token != token_str:
            raise NotA108DocstringException('Expected "%s", got "%s" instead' % (token_str, token))
        self.advance_to_next_token()

    def push_then_parse_then_pop(self, node):
        """A convenience method that will push the node onto the stack, then
        parse the element recursively, then pop this node off. This is used to
        push a node that has child definitions onto the stack so it is
        assigned the children appropriately, and then cleans up the stack.
        node: The DocNode to go on the stack.
        """
        self.push_node_on_stack(node)
        self.parse_element()
        self.pop_node_stack()

    def get_current_token(self):
        """Gets the current token."""
        return self.tokens[self.token_index]

    def advance_to_next_token(self):
        """Advances to the next token. Note: This does not throw an exception
        if there is not a following token, the pointer is incremented."""
        self.token_index += 1

    def add_as_child_node(self, node):
        """Adds a node as a child to the last element on the node stack.
        node: The node to add.
        """
        self.node_stack[-1].children.append(node)

    def push_node_on_stack(self, node):
        """Pushes a node onto the stack.
        node: The DocNode to push onto the stack.
        """
        self.node_stack.append(node)

    def pop_node_stack(self):
        """Pops a node off of the stack."""
        self.node_stack.pop(-1)

    def raise_if_not_all_tokens_consumed(self):
        """Checks to make sure all the tokens have been consumed, which is
        required for the final parsing step since the user may have added
        additional tokens that make it an invalid string.
        Example: '(int) -> str bool' is invalid.
        """
        if self.token_index < len(self.tokens):
            raise NotA108DocstringException

    
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
    return merged_docstring[:-1]  # Trim last space (TODO - do this better...)


def parse_csc108_docstring(full_docstring):
    """Takes the header line of a docstring which is supposed to be the
    docstring, and parses it. If parsing fails, a NotA108DocstringException
    is raised.
    Returns two nodes as a tuple: (Args tree DocNode, result tree DocNode).
    """
    line = trim_docstring_down_to_type_contract(full_docstring)
    parser = DocstringParser(line)
    return parser.args_node, parser.return_node
