"""
Top-level functions to mutate the astroid nodes with `end_col_offset` and
`end_lineno` properties. 

Where possible, the `end_col_offset` property is set by that of the node's last child.

    fromlineno
        - existing attribute
        - one-indexed
    end_lineno
        - new attribute
        - one-indexed
    col_offset
        - existing attribute
        - zero-indexed
        - located left of the first character
    end_col_offset
        - new attribute
        - zero-indexed
        - located right of the last character (essentially the string length)

In astroid/astroid/transforms.py, functions are registered to types in the
`transforms` dictionary in the TransformVisitor class. The traversal at
line 83 eventually leads to the transform called on each node at line 36,
within the _transform method.

Astroid Source:
https://github.com/PyCQA/astroid/blob/master/astroid/transforms.py
"""
import astroid
from astroid.transforms import TransformVisitor
import logging

CONSUMABLES = " \n\t\\"


# These nodes have no children, and their end_lineno and end_col_offset
# attributes are set based on their string representation (according to astroid).
# Goal: eventually replace the transforms for all the nodes in this list with the 
# predicate technique that uses more robust approach using searching, rather than
# simple length of string.
NODES_WITHOUT_CHILDREN = [
    astroid.AssignName,
    astroid.Break,
    astroid.Const,
    astroid.Continue,
    astroid.DelName,
    astroid.Ellipsis,
    astroid.Global,
    astroid.Import,
    astroid.ImportFrom,
    astroid.List,
    astroid.Name,
    astroid.Nonlocal,
    astroid.Pass,
    astroid.Yield
]

# These nodes have a child, and their end_lineno and end_col_offset
# attributes are set equal to those of their last child.
NODES_WITH_CHILDREN = [
    astroid.Assert,
    astroid.Assign,
    astroid.AsyncFor,
    astroid.AsyncFunctionDef,
    astroid.AsyncWith,
    astroid.AugAssign,
    astroid.Await,
    astroid.BinOp,
    astroid.BoolOp,
    astroid.Call,
    astroid.ClassDef,
    astroid.Compare,
    astroid.Comprehension,
    astroid.Decorators,
    astroid.Delete,
    astroid.ExceptHandler,
    astroid.ExtSlice,
    # astroid.Expr,  # need this here?
    astroid.For,
    astroid.FunctionDef,
    astroid.GeneratorExp,
    
    # TODO: need to fix elif (start) col_offset
    astroid.If,
    astroid.IfExp,
    astroid.Index,
    astroid.Keyword,
    astroid.Lambda,
    astroid.Module,
    astroid.Raise,
    astroid.Return,
    astroid.Starred,
    astroid.Subscript,
    astroid.TryExcept,
    astroid.TryFinally,
    astroid.UnaryOp,
    astroid.While,
    astroid.With,
    astroid.YieldFrom
]

# Predicate functions, for setting locations based on source code.
# Predicates can only return a single truthy value, because of how its used in
# `astroid/transforms.py`
# ====================================================
def _token_search(token):
    """
    @type token: string
    @rtype: function
    """
    def _is_token(s, index, node):
        """Fix to include certain tokens such as a paren, bracket, or brace.
        @type s: string
        @type index: int
        @type node: Astroid node
        @rtype: bool
        """
        return s[index] == token
    return _is_token

def _keyword_search(keyword):
    """
    @type keyword: string
    @rtype: function
    """
    def _is_keyword(s, index, node):
        """Search for a keyword. Right-to-left.
        @type s: string
        @type index: int
        @type node: Astroid node
        @rtype: bool
        """
        return s[index : index + len(keyword)] == keyword
    return _is_keyword

def _is_within_close_bracket(s, index, node):
    """Fix to include right ']'."""
    # print('>>>>>>', s, s[index], index, node.end_col_offset)
    if index >= len(s)-1: 
        return False
    return s[index] == ']' or s[index+1] == ']'

def _is_within_open_bracket(s, index, node):
    """Fix to include left '['."""
    # print('>>>>>>', s, index)
    if index < 1: 
        return False
    return s[index-1] == '['

def _is_attr_name(s, index, node):
    """Search for the name of the attribute. Left-to-right."""
    target_len = len(node.attrname)
    if index < target_len: 
        return False
    # print('---> "{}", "{}"'.format(s[index-target_len : index], node.attrname))
    return s[index-target_len+1 : index+1] == node.attrname

def _is_arg_name(s, index, node):
    """Search for the name of the argument. Right-to-left."""
    if not node.arg: 
        return False
    return s[index : index+len(node.arg)] == node.arg

def _set_slice_start(s, index, node):
    """Set slice locations, whether it has slice before it or not"""

    # check slice node has sibling subscript, i.e. if parent contains subscript.
    # if node.parent.get_children()

    # always start searching for the first [ after the ENDING POSITION of the parent's value node.
    # i.e. if we are on that line, and index is less than ending position just return false
    parent_value = node.parent.value
    if parent_value:
        parent_value_line = parent_value.fromlineno
        parent_value_end = parent_value.end_col_offset

        # assert: Slice() node will always be after `end_col_offset` of sibling Subscript()
        if parent_value_line > node.fromlineno or index < parent_value_end:
            return False

    # otherwise return the bool check
    return s[index-1] == '['

def _set_slice_end(s, index, node):
    """Set slice locations, whether it has slice before it or not"""
    if index >= len(s)-1: 
        return False
    return s[index+1] == ']'


# Nodes the require the source code for proper location setting
# Elements here are in the form
# (node class, predicate for start | None, predicate for end | None)
NODES_REQUIRING_SOURCE = [

    (astroid.AssignAttr, None, _is_attr_name),  
    (astroid.AsyncFor, _keyword_search('async'), None),
    (astroid.AsyncWith, _keyword_search('async'), None),
    (astroid.Attribute, None, _is_attr_name),
    (astroid.Call, None, _token_search(')')),
    (astroid.DelAttr, _keyword_search('del'), _is_attr_name),
    (astroid.DelName, _keyword_search('del'), None),
    (astroid.Dict, None, _token_search('}')),
    (astroid.DictComp, None, _token_search('}')),

    # FIXME: sometimes start/ending char does not exist.
    (astroid.Expr, _token_search('('), _token_search(')')),
    (astroid.ExtSlice, _token_search('['), _token_search(']')),
    (astroid.GeneratorExp, _token_search('('), _token_search(')')),
    (astroid.Index, _token_search('['), _token_search(']')),
    (astroid.Keyword, _is_arg_name, None),
    
    # TODO: missing *both* outer brackets
    (astroid.ListComp, _token_search('['), _token_search(']')),
    (astroid.Set, None, _token_search('}')),
    (astroid.SetComp, None, _token_search('}')),
    (astroid.Slice, _set_slice_start, _set_slice_end),
    # (astroid.Slice, _is_within_open_bracket, _is_within_close_bracket),
    (astroid.Subscript, None, _token_search(']')),
    (astroid.Tuple, _token_search('('), _token_search(')'))
]


# Configure logging
log_format = '%(asctime)s %(levelname)s %(message)s'
log_date_time_format = '%Y-%m-%d %H:%M:%S'  # removed millis
log_filename = 'python_ta/transforms/setendings_log.log'
logging.basicConfig(format=log_format, datefmt=log_date_time_format,
                    level=logging.WARNING)


def init_register_ending_setters(source_code):
    """Instantiate a visitor to transform the nodes.
    Register the transform functions on an instance of TransformVisitor.

    @type source_code: list of strings
    @rtype: TransformVisitor
    """
    ending_transformer = TransformVisitor()

    # Check consistency of astroid-provided fromlineno and col_offset attributes.
    for node_class in astroid.ALL_NODE_CLASSES:
        ending_transformer.register_transform(
            node_class,
            fix_start_attributes,
            lambda node: node.fromlineno is None or node.col_offset is None)

    # Ad hoc transformations
    ending_transformer.register_transform(astroid.Arguments, fix_start_attributes)
    ending_transformer.register_transform(astroid.Arguments, set_arguments)
    ending_transformer.register_transform(astroid.Slice, fix_slice(source_code))
    
    for node_class in NODES_WITHOUT_CHILDREN:
        ending_transformer.register_transform(node_class, set_without_children)
    for node_class in NODES_WITH_CHILDREN:
        ending_transformer.register_transform(node_class, set_from_last_child)

    # Nodes where the source code must also be provided.
    # source_code and the predicate functions get stored in the TransformVisitor
    for node_class, start_pred, end_pred in NODES_REQUIRING_SOURCE:
        if start_pred is not None:
            ending_transformer.register_transform(
                node_class, start_setter_from_source(source_code, start_pred))
        if end_pred is not None:
            ending_transformer.register_transform(
                node_class, end_setter_from_source(source_code, end_pred))

    # TODO: investigate these nodes, and create tests/transforms/etc when found.
    ending_transformer.register_transform(astroid.DictUnpack, discover_nodes)
    ending_transformer.register_transform(astroid.EmptyNode, discover_nodes)
    ending_transformer.register_transform(astroid.Exec, discover_nodes)
    ending_transformer.register_transform(astroid.Print, discover_nodes)
    ending_transformer.register_transform(astroid.Repr, discover_nodes)
    return ending_transformer


# Transform functions.
# These functions are called on individual nodes to either fix the
# `fromlineno` and `col_offset` properties of the nodes,
# or to set the `end_lineno` and `end_col_offset` attributes for a node.
# ====================================================
def discover_nodes(node):
    """Log to file and console when an elusive node is encountered, so it can
    be classified, and tested..
    @type node: Astroid node
    """
    # Some formatting for the code output
    output = [line for line in node.statement().as_string().strip().split('\n')]
    output = ['=' * 40] + output + ['=' * 40]
    message = '>>>>> Found elusive {} node. Context:\n\t{}'.format(node, '\n\t'.join(output))
    # Print to console, and log for persistence.
    print('\n' + message)
    logging.info(message)


def fix_slice(source_code):
    """
    The Slice node column positions are mostly set properly when it has (Const) 
    children, all it needs is to consume leading/trailing whitespace.
    Don't include '[' or ']' in the col_offset or end_col_offset.

    The main problem is when Slice node doesn't have children. 
    E.g "[:]", "[::]", "[:][:]", "[::][::]", ... yikes! The existing 
    col_offset of the slice node is set improperly to 0. And the end_col_offset 
    is also wrong. We fix it here.

    The idea is:
    • Start at the coords of fist parent Subscript in source code.
    • While there are children Subscript nodes, use its as_string to consume 
    these chars from the source code, and keep count of position cursor.
    • Consume the chars, moving cursor, until reach first position of ':'.
    • The caller function consumes whitespace left/right up to brackets, using
    predicate functions to check whether a bracket is encountered.

    @type source_code: list of strings
    """
    def _consume_subscripts(node):
        if node.last_child(): 
            return
        if not hasattr(node, 'end_lineno'): 
            set_without_children(node)

        line_i = node.parent.fromlineno - 1  # 1-based
        char_i = node.parent.col_offset      # 0-based

        # If Slice() has sibling Subscript() nodes, e.g. the last two Slice in
        # "n[:][:][:]", we search for the first '[' after the ENDING POSITION 
        # of the parent's value node.
        for sibling in node.parent.get_children():
            if isinstance(sibling, astroid.Subscript): 
                pass

        
        # The Wrong Buffer approach
        # >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

        # To solve the problem created by variations of "a[:][:]...",
        # consume all sibling Subscript node characters
        # sibling_buffer = ''
        # for sibling in node.parent.get_children():
        #     if isinstance(sibling, astroid.Subscript): 
        #         sibling_buffer += sibling.as_string()

        # # print(type(node.parent.value))

        
        # # Search the remaining lines
        # while sibling_buffer and line_i < len(source_code)-1:
        #     # at end of line, or skip comment line..
        #     if char_i == len(source_code[line_i]) - 1 or source_code[line_i][char_i] is '#': 
        #         char_i = 0
        #         line_i += 1

        #     # consume stuff from the buffer.
        #     if source_code[line_i][char_i] == sibling_buffer[0]:
        #         char_i += 1
        #         sibling_buffer = sibling_buffer[1:]
        #     elif source_code[line_i][char_i] in CONSUMABLES: 
        #         char_i += 1

        # The Wrong Buffer approach
        # <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<

        

        # now we can simply search for the ":" char since this Slice node
        # has no children.
        while source_code[line_i][char_i] != ':': 
            if char_i == len(source_code[line_i]) - 1 or source_code[line_i][char_i] is '#': 
                char_i = 0
                line_i += 1
            else: 
                char_i += 1

        

        node.fromlineno = line_i + 1
        node.end_col_offset = char_i  # temporary value because (_is_within_open_bracket, _is_within_close_bracket) transforms fix it. 
        node.col_offset = char_i

    return _consume_subscripts


def fix_start_attributes(node):
    """Some nodes don't always have the `col_offset` property set by Astroid:
    Comprehension, ExtSlice, Index, Keyword, Module, Slice.
    """
    assert node.fromlineno is not None, \
            'node {} doesn\'t have fromlineno set.'.format(node)

    # Log when this function is called.
    logging.info(str(node)[:-2])

    try:
        first_child = next(node.get_children())
        if node.fromlineno is None:
            node.fromlineno = first_child.fromlineno
        if node.col_offset is None:
            node.col_offset = first_child.col_offset

    except StopIteration:
        # No children. Go to the enclosing statement and use that.
        # This assumes that statement nodes will always have these attributes set.
        statement = node.statement()
        assert statement.fromlineno is not None and statement.col_offset is not None, \
            'Statement node {} doesn\'t have start attributes set.'.format(statement)

        if node.fromlineno is None:
            node.fromlineno = statement.fromlineno
        if node.col_offset is None:
            node.col_offset = statement.col_offset


def set_from_last_child(node):
    """Populate ending locations for astroid node based on its last child.

    Preconditions:
      - `node` must have a `last_child` (node).
      - `node` has col_offset property set.
    """
    last_child = _get_last_child(node)
    if not last_child: 
        set_without_children(node)
        return
    elif not hasattr(last_child, 'end_lineno'):  # Newly added for Slice() node.
        set_without_children(last_child)
    
    assert (last_child is not None and
            last_child.end_lineno is not None and
            last_child.end_col_offset is not None),\
            'ERROR: last_child ({}) of node ({}) is missing attributes.'\
            .format(last_child, node)

    node.end_lineno, node.end_col_offset = last_child.end_lineno, last_child.end_col_offset


def set_without_children(node):
    """Populate ending locations for nodes that are guaranteed to never have
    children. E.g. Const.

    These node's end_col_offset are currently assigned based on their
    computed string representation. This may differ from their actual
    source code representation, however (mainly whitespace).

    Precondition: `node` must not have a `last_child` (node).
    """
    if not hasattr(node, 'end_lineno'):
        node.end_lineno = node.fromlineno
    # FIXME: using the as_string() is a bad technique because many different
    # whitespace possibilities that may not be reflected in it!
    if not hasattr(node, 'end_col_offset'):
        node.end_col_offset = node.col_offset + len(node.as_string())


def set_arguments(node):
    """astroid.Arguments node is missing the col_offset, and has children only
    sometimes.
    Arguments node can be found in nodes: FunctionDef, Lambda.
    """
    if _get_last_child(node):
        set_from_last_child(node)
    else:  # node does not have children.
        # TODO: this should be replaced with the string parsing strategy
        node.end_lineno, node.end_col_offset = node.fromlineno, node.col_offset


def _get_last_child(node):
    """Returns the last child node, or None.
    Some nodes' last_child() attribute not set, e.g. astroid.Arguments.
    """
    if node.last_child():
        return node.last_child()
    else:
        # Get the first child from the `get_children` generator.
        skip_to_last_child = None  # save reference to last child.
        for skip_to_last_child in node.get_children():
            pass  # skip to last
        return skip_to_last_child  # postcondition: node, or None.


def end_setter_from_source(source_code, pred):
    """Returns a *function* that sets ending locations for a node from source.

    The basic technique is to do the following:
      1. Find the ending locations for the node based on its last child.
      2. Starting at that point, iterate through characters in the source code
         up to and including the first index that satisfies pred.

    pred is a function that takes a string and index and returns a bool,
    e.g. _is_close_paren
    """
    def set_endings_from_source(node):
        if not hasattr(node, 'end_col_offset'): 
            set_from_last_child(node)

        # Initialize counters. Note: we need to offset lineno,
        # since it's 1-indexed.
        end_col_offset, lineno = node.end_col_offset, node.end_lineno - 1

        # First, search the remaining part of the current end line.
        for j in range(end_col_offset, len(source_code[lineno])):
            if source_code[lineno][j] == '#': 
                break  # skip over comment lines
            if pred(source_code[lineno], j, node):
                temp = node.end_col_offset
                node.end_col_offset = j + 1
                return

        # If that doesn't work, search remaining lines
        for i in range(lineno + 1, len(source_code)):
            # Search each character
            for j in range(len(source_code[i])):
                if source_code[i][j] == '#': 
                    break  # skip over comment lines
                if pred(source_code[i], j, node):
                    temp_c = node.end_col_offset
                    temp_l = node.end_lineno
                    node.end_col_offset, node.end_lineno = j + 1, i + 1
                    return
                # only consume inert characters.
                elif source_code[i][j] not in CONSUMABLES: 
                    return

    return set_endings_from_source


def start_setter_from_source(source_code, pred):
    """Returns a *function* that sets start locations for a node from source.
    Recall `source_code`, `pred` are within the lexical scope of the returned function.

    The basic technique is to do the following:
      1. Find the start locations for the node (already set).
      2. Starting at that point, iterate through characters in the source code
         in reverse until reaching the first index that satisfies pred.

    pred is a function that takes a string and index and returns a bool,
    e.g. _is_open_paren
    """
    def set_start_from_source(node):
        # Initialize counters. Note: we need to offset lineno,
        # since it's 1-indexed.
        col_offset, lineno = node.col_offset, node.fromlineno - 1

        # First, search the remaining part of the current end line
        for j in range(col_offset, -1, -1):
            if pred(source_code[lineno], j, node):
                temp = node.col_offset
                node.col_offset = j
                return

        # If that doesn't work, search remaining lines
        for i in range(lineno - 1, -1, -1):
            # Search each character, right-to-left
            for j in range(len(source_code[i]) - 1, -1, -1):
                if pred(source_code[i], j, node):
                    node.end_col_offset, node.end_lineno = j, i + 1
                    return
                # only consume inert characters.
                elif source_code[i][j] not in CONSUMABLES: 
                    return

    return set_start_from_source
