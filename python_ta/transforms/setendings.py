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
    astroid.AssignAttr,
    astroid.AsyncFor,
    astroid.AsyncFunctionDef,
    astroid.AsyncWith,
    astroid.Attribute,
    astroid.AugAssign,
    astroid.Await,
    astroid.BinOp,
    astroid.BoolOp,
    astroid.Call,
    astroid.ClassDef,
    astroid.Compare,
    astroid.Comprehension,
    astroid.Decorators,
    astroid.DelAttr,
    astroid.Delete,
    # TODO: missing right }
    # [This one is tricky because there is no way to capture the last brace]
    astroid.Dict,
    # TODO: missing right }
    # [This one is tricky because there is no way to capture the last brace]
    astroid.DictComp,
    astroid.ExceptHandler,
    astroid.ExtSlice,
    # TODO: missing right paren
    # [This one is tricky because original paren are lost in astroid properties]
    astroid.Expr,
    astroid.For,
    astroid.FunctionDef,
    astroid.GeneratorExp,
    # TODO: need to fix elif (start) col_offset
    astroid.If,
    astroid.IfExp,
    astroid.Index,
    astroid.Keyword,
    astroid.Lambda,
    astroid.ListComp,
    astroid.Raise,
    astroid.Return,
    astroid.Set,
    astroid.SetComp,
    astroid.Slice,
    astroid.Starred,
    astroid.Subscript,
    astroid.TryExcept,
    astroid.TryFinally,
    astroid.Tuple,
    astroid.UnaryOp,
    astroid.While,
    astroid.With,
    astroid.YieldFrom
]


def init_register_ending_setters():
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

    for node_class in NODES_WITH_CHILDREN:
        ending_transformer.register_transform(node_class, set_from_last_child)
    for node_class in NODES_WITHOUT_CHILDREN:
        ending_transformer.register_transform(node_class, set_without_children)

    # Ad hoc transformations, due to inconsistencies in locations.
    ending_transformer.register_transform(astroid.Arguments, fix_start_attributes)
    ending_transformer.register_transform(astroid.Arguments, set_arguments)
    ending_transformer.register_transform(astroid.AssignAttr, set_assignattr)
    ending_transformer.register_transform(astroid.AsyncFor, lambda node: set_front_adjust(node, 6))
    ending_transformer.register_transform(astroid.AsyncFunctionDef, lambda node: set_front_adjust(node, 6))
    ending_transformer.register_transform(astroid.AsyncWith, lambda node: set_front_adjust(node, 6))
    ending_transformer.register_transform(astroid.DelAttr, lambda node: set_front_adjust(node, 4))
    ending_transformer.register_transform(astroid.DelName, lambda node: set_front_adjust(node, 4))
    ending_transformer.register_transform(astroid.Attribute, set_attribute)
    ending_transformer.register_transform(astroid.Await, set_await)
    ending_transformer.register_transform(astroid.Call, lambda node: set_end_adjust(node, 1))
    ending_transformer.register_transform(astroid.Comprehension, lambda node: set_front_adjust(node, 4))
    ending_transformer.register_transform(astroid.GeneratorExp, lambda node: set_front_adjust(node, 1))
    ending_transformer.register_transform(astroid.GeneratorExp, lambda node: set_end_adjust(node, 1))
    ending_transformer.register_transform(astroid.Raise, lambda node: set_end_adjust(node, 1))
    ending_transformer.register_transform(astroid.Index, lambda node: set_front_adjust(node, 1))
    ending_transformer.register_transform(astroid.Index, lambda node: set_end_adjust(node, 1))
    ending_transformer.register_transform(astroid.Keyword, set_keyword)
    ending_transformer.register_transform(astroid.ListComp, lambda node: set_front_adjust(node, 1))
    ending_transformer.register_transform(astroid.ListComp, lambda node: set_end_adjust(node, 1))
    ending_transformer.register_transform(astroid.Set, lambda node: set_end_adjust(node, 1))
    ending_transformer.register_transform(astroid.SetComp, lambda node: set_end_adjust(node, 1))
    ending_transformer.register_transform(astroid.Slice, set_slice)
    ending_transformer.register_transform(astroid.Tuple, set_tuple)

    # TODO: investigate these nodes.
    # ending_transformer.register_transform(astroid.DictUnpack, set_from_last_child)
    # ending_transformer.register_transform(astroid.EmptyNode, set_from_last_child)
    # ending_transformer.register_transform(astroid.Exec, set_from_last_child)
    # ending_transformer.register_transform(astroid.Module, set_without_col_offset)
    # ending_transformer.register_transform(astroid.Print, set_from_last_child)
    # ending_transformer.register_transform(astroid.Repr, set_from_last_child)
    return ending_transformer


# Transform functions.
# These functions are called on individual nodes to either fix the
# `fromlineno` and `col_offset` properties of the nodes,
# or to set the `end_lineno` and `end_col_offset` attributes for a node.

def set_front_adjust(node, adjust=0):
    """Include the 'async' keyword in expressions for all Async* nodes.
    Include the 'del' keyword in expressions for all Del* nodes.
    Include the 'for' keyword in expressions for all Comprehension nodes.
    Include the first parens/brackets for all nodes: GeneratorExp, ListComp.
    Precondition: col_offset has been set.
    """
    node.col_offset -= adjust


def set_end_adjust(node, adjust=0):
    """end_col_offset missing right parens/brackets/braces on nodes:
    Call, GeneratorExp, Raise, ExtSlice, ListComp, Set
    """
    node.end_col_offset += adjust


# TODO: Log when this function is called.
def fix_start_attributes(node):
    """Some nodes don't always have the `col_offset` property set by Astroid:
    astroid.Comprehension, astroid.ExtSlice, astroid.Index,
    astroid.Keyword, astroid.Module, astroid.Slice

    Question: is the 'fromlineno' attribute always set?
    """
    assert node.fromlineno is not None, \
            'node {} doesn\'t have fromlineno set.'.format(node)

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


def fix_start_attributes_arguments(node):
    """Fix the col_offset attribute for astroid.Argument nodes.
    Precondition: node does not have children."""
    # set from col offset of parent FunctionDef node plus len of name.
    parent_node = node.parent
    if isinstance(parent_node, astroid.FunctionDef):
        # account for 'def', name of the signature, and '('
        node.col_offset = parent_node.col_offset + len(parent_node.name) + 5
    elif isinstance(parent_node, astroid.Lambda):
        # account for 'lambda'
        node.col_offset = parent_node.col_offset + 6
        # If there are no arguments, this node takes up no space


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
    else:
        fix_start_attributes_arguments(node)
        node.end_lineno, node.end_col_offset = node.fromlineno, node.col_offset


def set_assignattr(node):
    """astroid.AssignAttr node should be set by the left and
    right side of the dot operator. Originally it would use 'self' rather than 
    'self.name'. We can't use the parent node as `set_attribute` does.
    """
    node.end_col_offset = node.col_offset + len(node.as_string())


def set_attribute(node):
    """Setting the attribute node by its last child wouldn't include
    the attribute in determining the end_col_offset, i.e. it was originally 
    set by left side of dot operator, but it should use both sides.
    """
    node.end_col_offset = node.col_offset + len(node.parent.as_string())


def set_await(node):
    """Setting end_col_offset by last child (i.e. arguments.Name) didn't 
    capture the left and right parenthesis in the arguments.Call node.
    """
    node.end_col_offset = node.col_offset + len(node.as_string())


def set_keyword(node):
    """Setting the missing col_offset by last child didn't capture the keyword 
    name. Determine col_offset by the index of the keyword string relative
    to its parent.
    """
    node_str = node.as_string()
    outer = node.statement()
    assert node_str is not None, \
            'node {} string cannot be used to find index.'.format(node)
    node.col_offset = outer.col_offset + outer.as_string().index(node_str)


def set_slice(node):
    """Determine end_col_offset by adding to the string length of the
    node. Also adjust col_offset by one to include the left bracket.
    Useful for nodes consisting of [1: ].
    """
    node.end_col_offset = node.col_offset + len(node.as_string()) + 1
    node.col_offset -= 1


def set_tuple(node):
    """Determine end_col_offset by adding to the string length of the
    node. Also adjust col_offset by one to include the left bracket.
    Useful for nodes consisting of (1, ).
    """
    node.col_offset -= 1
    node.end_col_offset = node.col_offset + len(node.as_string())


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
