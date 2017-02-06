"""
Top-level functions to mutate the astroid nodes with `end_col_offset` and
`end_lineno` properties.

In astroid/astroid/transforms.py, functions are registered to types in the
`transforms` dictionary in the TransformVisitor class. The traversal at
line 83 eventually leads to the transform called on each node at line 36,
within the _transform method.

Astroid Source:
https://github.com/PyCQA/astroid/blob/master/astroid/transforms.py

If possible, set the `end_col_offset` property by that of the node's last child.
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
    # TODO: This one identifies only the expression to the left of the period,
    # and not the name of the attribute.
    # Given 'self.name = 10', it will highlight 'self' rather than 'self.name'
    astroid.AssignAttr,
    # TODO: Include the 'async' keyword in expressions for all Async* nodes.
    astroid.AsyncFor,
    astroid.AsyncFunctionDef,
    astroid.AsyncWith,
    # TODO: Same problem as AssignAttr (attribute missing)
    astroid.Attribute,
    astroid.AugAssign,
    astroid.Await,
    astroid.BinOp,
    astroid.BoolOp,
    # TODO: missing right parens
    astroid.Call,
    astroid.ClassDef,
    astroid.Compare,
    # TODO: missing right parens (note: only if decorator takes args)
    astroid.Decorators,
    # TODO: missing keyword 'del' and attribute name
    astroid.DelAttr,
    astroid.Delete,
    # TODO: missing right }
    astroid.Dict,
    # TODO: missing right }
    astroid.DictComp,
    astroid.ExceptHandler,
    # TODO: missing *both* outer brackets
    astroid.ExtSlice,
    # TODO: missing right paren
    astroid.Expr,
    astroid.For,
    astroid.FunctionDef,
    # TODO: missing *both* outer parens
    astroid.GeneratorExp,
    # TODO: need to fix elif (start) col_offset
    astroid.If,
    astroid.IfExp,
    # TODO: missing *both* outer brackets
    astroid.Index,
    # TODO: would be good to see the name of the keyword as well
    astroid.Keyword,
    astroid.Lambda,
    # TODO: missing *both* outer brackets
    astroid.ListComp,
    astroid.Module,
    astroid.Raise,
    astroid.Return,
    # TODO: missing right }
    astroid.Set,
    # TODO: missing right }
    astroid.SetComp,
    # TODO: missing *both* outer brackets
    astroid.Slice,
    astroid.Starred,
    # TODO: missing right ]
    astroid.Subscript,
    astroid.TryExcept,
    astroid.TryFinally,
    astroid.UnaryOp,
    astroid.While,
    astroid.With,
    astroid.YieldFrom
]


# Helpers for setting locations based on source code.
def _is_close_paren(s, index):
    return s[index] == ')'


def _is_open_paren(s, index):
    return s[index] == '('


# Nodes the require the source code for proper location setting
# Elements here are in the form
# (node class, predicate for start | None, predicate for end | None)
NODES_REQUIRING_SOURCE = [
    (astroid.Comprehension, None, _is_close_paren),
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

    assert (last_child is not None and
            last_child.end_lineno is not None and
            last_child.end_col_offset is not None),\
        'ERROR: last_child is missing or is missing attributes.'

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
        col_offset, lineno = node.end_col_offset, node.end_lineno - 1

        # First, search the remaining part of the current end line
        for j in range(col_offset, len(source_code[lineno])):
            if pred(source_code[lineno], j):
                node.end_col_offset = j + 1
                return

        # If that doesn't work, search remaining lines
        for i in range(lineno + 1, len(source_code)):
            for j in range(len(source_code[i])):
                if pred(source_code[i], j):
                    node.end_col_offset, node.end_lineno = j + 1, i + 1
                    return

    return set_endings_from_source


def start_setter_from_source(source_code, pred):
    """Returns a *function* that sets start locations for a node from source.

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
        col_offset, lineno = node.col_offset - 1, node.fromlineno - 1

        # First, search the remaining part of the current end line
        for j in range(col_offset, -1, -1):
            if pred(source_code[lineno], j):
                node.col_offset = j
                return

        # If that doesn't work, search remaining lines
        for i in range(lineno - 1, -1, -1):
            for j in range(len(source_code[i]) - 1, -1, -1):
                if pred(source_code[i], j):
                    node.end_col_offset, node.end_lineno = j, i + 1
                    return

    return set_start_from_source


# Make this module a pylint plugin
def register(linter):
    old_get_ast = linter.get_ast
    def new_get_ast(filepath, modname):
        ast = old_get_ast(filepath, modname)
        with open(filepath) as f:
            source_code = f.readlines()
        ending_transformer = TransformVisitor()
        register_transforms(source_code, ending_transformer)
        ending_transformer.visit(ast)
        return ast

    linter.get_ast = new_get_ast


def register_transforms(source_code, obj):
    # Check consistency of astroid-provided fromlineno and col_offset attributes.
    for node_class in astroid.ALL_NODE_CLASSES:
        obj.register_transform(
            node_class,
            fix_start_attributes,
            lambda node: node.fromlineno is None or node.col_offset is None)

    # Ad hoc transformations
        obj.register_transform(astroid.Arguments, fix_start_attributes)
        obj.register_transform(astroid.Arguments, set_arguments)

    for node_class in NODES_WITH_CHILDREN:
        obj.register_transform(node_class, set_from_last_child)
    for node_class in NODES_WITHOUT_CHILDREN:
        obj.register_transform(node_class, set_without_children)

    # Nodes where the source code must also be provided.
    for node_class, start_pred, end_pred in NODES_REQUIRING_SOURCE:
        if start_pred is not None:
            obj.register_transform(
                node_class, start_setter_from_source(source_code, start_pred))
        if end_pred is not None:
            obj.register_transform(
                node_class, end_setter_from_source(source_code, end_pred))

    # TODO: investigate these nodes, and create tests/transforms/etc when found.
    obj.register_transform(astroid.DictUnpack, discover_nodes)
    obj.register_transform(astroid.EmptyNode, discover_nodes)
    obj.register_transform(astroid.Exec, discover_nodes)
    obj.register_transform(astroid.Print, discover_nodes)
    obj.register_transform(astroid.Repr, discover_nodes)
