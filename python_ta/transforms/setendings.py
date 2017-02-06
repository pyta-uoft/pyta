"""
Top-level functions to mutate the astroid nodes with `end_col_offset` and
`end_lineno` properties. 

Where possible, the `end_col_offset` property is set by that of the node's last child.

    fromlineno
        - existing attribute.
        - one-indexed
    end_lineno
        - new attribute
        - one-indexed
    col_offset
        - existing attribute.
        - zero-indexed
        - located left of the first character.
    end_col_offset
        - new attribute
        - zero-indexed
        - located right of the last character (essentially the string length).

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


# These nodes have no children, and their end_lineno and end_col_offset
# attributes are set based on their string representation (according to astroid).
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
    
    # TODO: missing right parens (note: only if decorator takes args)
    astroid.Decorators,
    
    # TODO: missing keyword 'del' and attribute name
    astroid.DelAttr,
    astroid.Delete,
    astroid.ExceptHandler,
    
    # TODO: missing *both* outer brackets
    astroid.ExtSlice,  # Buggy because children (index, slice) already use the brackets.
    astroid.Expr,
    astroid.For,
    astroid.FunctionDef,
    astroid.GeneratorExp,
    
    # TODO: need to fix elif (start) col_offset
    astroid.If,
    astroid.IfExp,
    
    # TODO: would be good to see the name of the keyword as well
    astroid.Keyword,
    astroid.Lambda,
    astroid.Module,
    astroid.Raise,
    astroid.Return,
    # astroid.Slice,
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
def _is_close_paren(s, index, node):
    """(string, int, node) --> bool
    Fix to include right )"""
    return s[index] == ')'

def _is_open_paren(s, index, node):
    """(string, int, node) --> bool
    Fix to include left ("""
    return s[index] == '('

def _is_close_brace(s, index, node):
    """(string, int, node) --> bool
    Fix to include right }"""
    return s[index] == '}'

def _is_open_brace(s, index, node):
    """(string, int, node) --> bool
    Fix to include left {"""
    return s[index] == '{'

def _is_close_bracket(s, index, node):
    """(string, int, node) --> bool
    Fix to include right ]"""
    return s[index] == ']'

def _is_open_bracket(s, index, node):
    """(string, int, node) --> bool
    Fix to include left ["""
    return s[index] == '['

def _is_for(s, index, node):
    """(string, int, node) --> bool
    Search for beginning of the `for`. [TODO: search for the whole keyword.]
    """
    return s[index] == 'f'

def _is_async(s, index, node):
    """(string, int, node) --> bool
    Search for beginning of the `async`. [TODO: search for the whole keyword.]
    """
    return s[index] == 'a'

def _is_attr_name(s, index, node):
    """(string, int, node) --> bool
    Search for the name of the attribute.
    """
    target_len = len(node.attrname)
    if index < target_len: return False
    # print('---> "{}", "{}"'.format(s[index-target_len : index], node.attrname))
    return s[index-target_len+1 : index+1] == node.attrname


# Nodes the require the source code for proper location setting
# Elements here are in the form
# (node class, predicate for start | None, predicate for end | None)
NODES_REQUIRING_SOURCE = [

    (astroid.AssignAttr, None, _is_attr_name),  
    (astroid.AsyncFor, _is_async, None),
    (astroid.Attribute, None, _is_attr_name),
    (astroid.Call, None, _is_close_paren),
    (astroid.Comprehension, _is_for, _is_close_paren),
    (astroid.Dict, None, _is_close_brace),
    
    # TODO: missing right }
    (astroid.DictComp, None, _is_close_brace),

    # FIXME: sometimes start/ending char does not exist.
    (astroid.Expr, _is_open_paren, _is_close_paren),

    # TODO: missing *both* outer brackets
    (astroid.ExtSlice, _is_open_bracket, _is_close_bracket),
    (astroid.GeneratorExp, _is_open_paren, None),
    (astroid.Index, _is_open_bracket, _is_close_bracket),
    
    # TODO: missing *both* outer brackets
    (astroid.ListComp, _is_open_bracket, _is_close_bracket),
    (astroid.Set, None, _is_close_brace),
    (astroid.SetComp, None, _is_close_brace),
    
    # TODO: missing *both* outer brackets
    (astroid.Slice, _is_open_bracket, _is_close_bracket),
    (astroid.Tuple, _is_open_paren, _is_close_paren)
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
    
    for node_class in NODES_WITH_CHILDREN:
        ending_transformer.register_transform(node_class, set_from_last_child)
    for node_class in NODES_WITHOUT_CHILDREN:
        ending_transformer.register_transform(node_class, set_without_children)

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

def discover_nodes(node):
    """Log to file and console when an elusive node is encountered, so it can
    be classified, and tested..
    """
    # Some formatting for the code output
    output = [line for line in node.statement().as_string().strip().split('\n')]
    output = ['=' * 40] + output + ['=' * 40]
    message = '>>>>> Found elusive {} node. Context:\n\t{}'.format(node, '\n\t'.join(output))
    # Print to console, and log for persistence.
    print('\n' + message)
    logging.info(message)


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

    # if 'AssignAttr' in str(node):
    #     print(node.attrname)
    #     print(node.expr)
    #     print('*'*70)
    #     print('*'*70)
    
    if not last_child: 
        set_without_children(node)
        return
    
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
    node.end_lineno = node.fromlineno
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


DEBUG = 0


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
        set_from_last_child(node)

        # Initialize counters. Note: we need to offset lineno,
        # since it's 1-indexed.
        # TBD: should this be 'end_col_offset' instead of 'col_offset'?
        end_col_offset, lineno = node.end_col_offset, node.end_lineno - 1

        consumables = " \\"

        # temp1 = ''
        # temp2 = ''

        # First, search the remaining part of the current end line.
        # Include last char in the start of search, incase already set??? no
        # end_char_location = end_col_offset - 1
        for j in range(end_col_offset, len(source_code[lineno])):
            # temp1 += source_code[lineno][j]
            
            if DEBUG:
                print('"{}", "{}", search: {}-{}-{}, {}, set_endings_from_source, COL.'\
                    .format(source_code[lineno][j], 
                            source_code[lineno], 
                            end_col_offset, 
                            j, 
                            len(source_code[lineno]), 
                            node ))
            
            if pred(source_code[lineno], j, node):
                temp = node.end_col_offset
                node.end_col_offset = j + 1
                if DEBUG:
                    print('end_col_offset ({}-->{})'.format(temp, node.end_col_offset))
                return

        # If that doesn't work, search remaining lines, 'i'.
        for i in range(lineno + 1, len(source_code)):
            # temp2 += source_code[lineno][i]
            # print(source_code[lineno][i], source_code[lineno])
            
            # Search each character 'j' in line 'i'.
            for j in range(len(source_code[i])):

                if DEBUG:
                    print('"{}", "{}", search: {}-{}-{}, {}, set_endings_from_source, LINE.'\
                        .format(source_code[i][j], 
                                source_code[i], 
                                0, 
                                j, 
                                len(source_code[i]), 
                                node ))

                if pred(source_code[i], j, node):
                    temp_c = node.end_col_offset
                    temp_l = node.end_lineno
                    node.end_col_offset, node.end_lineno = j + 1, i + 1
                    if DEBUG:
                        print('end_col_offset ({}-->{})'.format(temp_c, node.end_col_offset))
                        print('end_lineno ({}-->{})'.format(temp_l, node.end_lineno))
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
                node.col_offset = j
                return

        # If that doesn't work, search remaining lines
        for i in range(lineno - 1, -1, -1):
            for j in range(len(source_code[i]) - 1, -1, -1):
                if pred(source_code[i], j, node):
                    node.end_col_offset, node.end_lineno = j, i + 1
                    return

    return set_start_from_source
