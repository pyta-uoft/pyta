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

# Note this is preliminary data. These nodes are not guaranteed to never have
# children. Nodes are removed from this list manually on contradiction.
# Any contradictions to this list will be raised as assertion exception.
NO_CHILDREN_TYPE = [astroid.AssignName, astroid.Break, astroid.Const, 
    astroid.Continue, astroid.DelName, astroid.Ellipsis, astroid.Global, 
    astroid.Import, astroid.ImportFrom, astroid.Name, astroid.Nonlocal, 
    astroid.Pass, astroid.Yield
]

def init_register_ending_setters():
    """Instantiate a visitor to transform the nodes.
    Register the transform functions on an instance of TransformVisitor.
    """
    ending_transformer = TransformVisitor()
    ending_transformer.register_transform(astroid.Arguments, set_arguments)
    ending_transformer.register_transform(astroid.Assert, set_from_last_child)
    ending_transformer.register_transform(astroid.Assign, set_from_last_child)
    ending_transformer.register_transform(astroid.AssignAttr, set_from_last_child)
    ending_transformer.register_transform(astroid.AssignName, set_without_children)
    ending_transformer.register_transform(astroid.AsyncFor, set_from_last_child)
    ending_transformer.register_transform(astroid.AsyncFunctionDef, set_from_last_child)
    ending_transformer.register_transform(astroid.AsyncWith, set_from_last_child)
    ending_transformer.register_transform(astroid.Attribute, set_from_last_child)
    ending_transformer.register_transform(astroid.AugAssign, set_from_last_child)
    ending_transformer.register_transform(astroid.Await, set_from_last_child)
    ending_transformer.register_transform(astroid.BinOp, set_from_last_child)
    ending_transformer.register_transform(astroid.BoolOp, set_from_last_child)
    ending_transformer.register_transform(astroid.Break, set_without_children)
    ending_transformer.register_transform(astroid.Call, set_from_last_child)
    ending_transformer.register_transform(astroid.ClassDef, set_from_last_child)
    ending_transformer.register_transform(astroid.Compare, set_from_last_child)
    ending_transformer.register_transform(astroid.Comprehension, set_without_col_offset)
    ending_transformer.register_transform(astroid.Const, set_without_children)
    ending_transformer.register_transform(astroid.Continue, set_without_children)
    ending_transformer.register_transform(astroid.Decorators, set_from_last_child)
    ending_transformer.register_transform(astroid.DelAttr, set_from_last_child)
    ending_transformer.register_transform(astroid.Delete, set_from_last_child)
    ending_transformer.register_transform(astroid.DelName, set_without_children)
    ending_transformer.register_transform(astroid.Dict, set_from_last_child)
    ending_transformer.register_transform(astroid.DictComp, set_from_last_child)
    # ending_transformer.register_transform(astroid.DictUnpack, set_from_last_child)
    ending_transformer.register_transform(astroid.Ellipsis, set_without_children)
    # ending_transformer.register_transform(astroid.EmptyNode, set_from_last_child)
    ending_transformer.register_transform(astroid.ExceptHandler, set_from_last_child)
    # ending_transformer.register_transform(astroid.Exec, set_from_last_child)
    ending_transformer.register_transform(astroid.Expr, set_from_last_child)
    ending_transformer.register_transform(astroid.ExtSlice, set_without_col_offset)
    ending_transformer.register_transform(astroid.For, set_from_last_child)
    ending_transformer.register_transform(astroid.FunctionDef, set_from_last_child)
    ending_transformer.register_transform(astroid.GeneratorExp, set_from_last_child)
    ending_transformer.register_transform(astroid.Global, set_without_children)
    ending_transformer.register_transform(astroid.If, set_from_last_child)
    ending_transformer.register_transform(astroid.IfExp, set_from_last_child)
    ending_transformer.register_transform(astroid.Import, set_without_children)
    ending_transformer.register_transform(astroid.ImportFrom, set_without_children)
    ending_transformer.register_transform(astroid.Index, set_without_col_offset)
    ending_transformer.register_transform(astroid.Keyword, set_without_col_offset)
    ending_transformer.register_transform(astroid.Lambda, set_from_last_child)
    ending_transformer.register_transform(astroid.List, set_without_children)
    ending_transformer.register_transform(astroid.ListComp, set_from_last_child)
    # ending_transformer.register_transform(astroid.Module, set_without_col_offset)
    ending_transformer.register_transform(astroid.Name, set_without_children)
    ending_transformer.register_transform(astroid.Nonlocal, set_without_children)
    ending_transformer.register_transform(astroid.Pass, set_without_children)
    # ending_transformer.register_transform(astroid.Print, set_from_last_child)
    ending_transformer.register_transform(astroid.Raise, set_from_last_child)
    # ending_transformer.register_transform(astroid.Repr, set_from_last_child)
    ending_transformer.register_transform(astroid.Return, set_from_last_child)
    ending_transformer.register_transform(astroid.Set, set_from_last_child)
    ending_transformer.register_transform(astroid.SetComp, set_from_last_child)
    ending_transformer.register_transform(astroid.Slice, set_without_col_offset)
    ending_transformer.register_transform(astroid.Starred, set_from_last_child)
    ending_transformer.register_transform(astroid.Subscript, set_from_last_child)
    ending_transformer.register_transform(astroid.TryExcept, set_from_last_child)
    ending_transformer.register_transform(astroid.TryFinally, set_from_last_child)
    ending_transformer.register_transform(astroid.Tuple, set_from_last_child)
    ending_transformer.register_transform(astroid.UnaryOp, set_from_last_child)
    ending_transformer.register_transform(astroid.While, set_from_last_child)
    ending_transformer.register_transform(astroid.With, set_from_last_child)
    ending_transformer.register_transform(astroid.Yield, set_without_children)
    ending_transformer.register_transform(astroid.YieldFrom, set_from_last_child)
    return ending_transformer

def set_end_col_offset_by_string(node):
    """Nodes without children can get end_col_offset by length of string, with
    the as_string attribute.
    """
    node.end_col_offset = node.col_offset + len(node.as_string())

def set_end_col_offset(node, last_child=None):
    """Nodes with children get end_col_offset by length of string of last child.
    Postorder setting of children first yields precondition: if a node has the
    property set, then all of its children are set.
    """
    node.end_col_offset = last_child.end_col_offset

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

def _set_col_offset_by_child(node):
    """Some nodes don't always have the `col_offset` property set by Astroid:
    astroid.Comprehension, astroid.ExtSlice, astroid.Index,
    astroid.Keyword, astroid.Module, astroid.Slice
    """
    # Get col_offset from first child from generator.
    node.col_offset = next(node.get_children()).col_offset

# Define the functions to transform the nodes.
# These functions are registered to their respective node type with the
# register_transform function.
# Mutates the nodes, adding the properties: `end_lineno`, `end_col_offset`.
def set_from_last_child(node):
    """General function called by many of the other transform functions.
    Populate ending locations for astroid node.
    Precondition: `node` must have a `last_child` (node).
    """
    last_child = _get_last_child(node)
    assert node.col_offset is not None, '''ERROR:️ node's col_offset property not
        set on node {}. register the transform function `set_without_col_offset`
        instead.'''.format(node)
    assert last_child, '''ERROR:️ {} node must have children to set props.
        Context:\n{}'''.format(node, node.as_string())
    assert last_child.tolineno, '''ERROR:️ tolineno is None but should exist
        on node: {}. Context: {}'''.format(last_child, last_child.as_string())
    assert last_child.end_lineno is not None, '''ERROR:️ end_lineno is None but
        should be set first in preorder traversal on node: {}. Context: {}
        '''.format(last_child, last_child.as_string())
    assert last_child.end_col_offset is not None, '''ERROR:️ last child 
        end_col_offset should not be None if used to set others. 
        Node {}.'''.format(last_child)
    node.end_lineno = last_child.tolineno
    set_end_col_offset(node, last_child)

def set_without_children(node):
    """Populate ending locations for nodes that are guaranteed to never have
    children. E.g. Const.
    Precondition: `node` must not have a `last_child` (node).
    """
    last_child = _get_last_child(node)  # Only used for assert.
    assert node.col_offset is not None, '''ERROR:️ node's col_offset property not
        set on node: {}. register the transform function `set_without_col_offset`
        instead.'''.format(node)
    assert node.tolineno, '''ERROR:️ tolineno is None but should be set by 
        asteroid on node: {}. Context: {}'''.format(node, node.as_string())
    assert hasattr(node, 'as_string'), '''ERROR:️ node {} must have the 
        .as_string method.'''.format(node)
    assert not last_child or type(node) not in NO_CHILDREN_TYPE, '''
        ERROR:️ Contradiction found. {} node in NO_CHILDREN_TYPE has children 
        ({}). Suggestion: remove node from the list. Context:\n{}'''.format(
            node, last_child, node.as_string())
    node.end_lineno = node.tolineno
    set_end_col_offset_by_string(node)

def set_without_col_offset(node):
    """Some nodes don't always have the `col_offset` property set by Astroid:
    astroid.Comprehension, astroid.ExtSlice, astroid.Index,
    astroid.Keyword, astroid.Module, astroid.Slice
    """
    if node.col_offset is None:
        _set_col_offset_by_child(node)
    set_from_last_child(node)

def set_arguments(node):
    """astroid.Arguments node is missing the col_offset, and has children only
    sometimes.
    Arguments node can be found in nodes: FunctionDef, Lambda.
    """
    if _get_last_child(node):
        _set_col_offset_by_child(node)
        set_from_last_child(node)
    else:
        # set from col offset of parent FunctionDef node plus len of name.
        parent_node = node.parent
        if isinstance(parent_node, astroid.FunctionDef):
            # account for 'def', name of the signature, and '('
            node.col_offset = parent_node.col_offset + len(parent_node.name) + 5
        elif isinstance(parent_node, astroid.Lambda):
            # account for 'lambda :'
            node.col_offset = parent_node.col_offset + 7
        set_without_children(node)
