"""
Top-level functions to mutate the astroid nodes with `end_col_offset` and
`end_lineno` properties.

In astroid/astroid/transforms.py, functions are registered to types in the 
`transforms` dictionary in the TransformVisitor class. The traversal at 
line 83 eventually leads to the transform called on each node at line 36, 
within the _transform method.

If possible, set the `end_col_offset` property by that of the node's last child.
"""

import astroid
from astroid.transforms import TransformVisitor
import logging

# Set the log level (DEBUG, ERROR, ...), and message format.
logging.basicConfig(format='', level=logging.DEBUG)

# Note this is preliminary data. These nodes are not guaranteed to never have
# children. Nodes are removed from this list manually on contradiction.
# Any contradictions to this list will be raised as exception.
NO_CHILDREN_TYPE = [astroid.AssignName, astroid.Break, 
            astroid.Const, astroid.DelName, astroid.Ellipsis, astroid.Global, 
            astroid.Import, astroid.ImportFrom, astroid.List, astroid.Name, 
            astroid.Nonlocal, astroid.Pass, astroid.Yield]

def init_register_ending_setters():
    """Instantiate a visitor to transform the nodes.
    Register the transform functions on an instance of TransformVisitor.
    """
    ending_transformer = TransformVisitor()
    ending_transformer.register_transform(astroid.Arguments, set_general)
    ending_transformer.register_transform(astroid.Assert, set_general)
    ending_transformer.register_transform(astroid.Assign, set_general)
    ending_transformer.register_transform(astroid.AssignAttr, set_general)
    # ending_transformer.register_transform(astroid.AssignName, set_general)
    # ending_transformer.register_transform(astroid.AsyncFor, set_general)
    # ending_transformer.register_transform(astroid.AsyncFunctionDef, set_general)
    # ending_transformer.register_transform(astroid.AsyncWith, set_general)
    # ending_transformer.register_transform(astroid.Attribute, set_general)
    # ending_transformer.register_transform(astroid.AugAssign, set_general)
    # ending_transformer.register_transform(astroid.Await, set_general)
    ending_transformer.register_transform(astroid.BinOp, set_general)
    # ending_transformer.register_transform(astroid.BoolOp, set_general)
    # ending_transformer.register_transform(astroid.Break, set_general)
    # ending_transformer.register_transform(astroid.Call, set_general)
    # ending_transformer.register_transform(astroid.ClassDef, set_general)
    # ending_transformer.register_transform(astroid.Compare, set_general)
    # ending_transformer.register_transform(astroid.Comprehension, set_general)
    ending_transformer.register_transform(astroid.Const, 
                                                set_without_children)
    # ending_transformer.register_transform(astroid.Continue, set_general)
    # ending_transformer.register_transform(astroid.Decorators, set_general)
    # ending_transformer.register_transform(astroid.DelAttr, set_general)
    # ending_transformer.register_transform(astroid.Delete, set_general)
    # ending_transformer.register_transform(astroid.DelName, set_general)
    # ending_transformer.register_transform(astroid.Dict, set_general)
    # ending_transformer.register_transform(astroid.DictComp, set_general)
    # ending_transformer.register_transform(astroid.Ellipsis, set_general)
    # ending_transformer.register_transform(astroid.ExceptHandler, set_general)
    # ending_transformer.register_transform(astroid.Expr, set_general)
    # ending_transformer.register_transform(astroid.ExtSlice, set_general)
    # TODO: attach more nodes with their transform functions here...

    return ending_transformer

def set_end_lineno(node, last_child=None):
    """Set `end_lineno` property by the last child, if possible.
    """
    assert node.tolineno, '''ERROR:️ tolineno is None but should be set by 
        asteroid on node: {}. Context: {}'''.format(node, node.as_string())
    if last_child:
        node.end_lineno = last_child.tolineno
    else:
        node.end_lineno = node.tolineno

def set_end_col_offset_by_string(node, last_child=None):
    """Nodes without children can get end_col_offset by length of string.
    Nodes with children get end_col_offset by length of string of last child.
    Hopefully this works without problems.
    """
    # TODO: refactor some repetitive code in these two code blocks?
    if last_child:
        assert hasattr(last_child, 'as_string'), '''ERROR:️ node {} must have the
            .as_string property.'''.format(last_child)
        # Some nodes have col_offset prop not set. e.g. astroid.Arguments..
        assert last_child.col_offset is not None, '''ERROR:️ node {} last_child 
            has col_offset == None, which we need to set node's col_offset.
            '''.format(last_child)
        node.col_offset = last_child.col_offset
        # print('\n before:', node.col_offset)
        # print('\n node:', node)
        # print('\n col_offset1:', last_child.col_offset)
        node.end_col_offset = last_child.col_offset + len(last_child.as_string())
    else:  # No children..
        assert hasattr(node, 'as_string'), '''ERROR:️ node {} must have the 
            .as_string property.'''.format(node)
        # Some nodes have col_offset prop not set. e.g. astroid.Arguments..
        if node.col_offset is None:
            # Get col_offset from first child from generator.
            first_child = next(node.get_children())
            # print('\n first_child:', first_child)
            node.col_offset = first_child.col_offset
    
        # print('\n node:', node)
        # print('\n col_offset2:', node.col_offset)
        node.end_col_offset = node.col_offset + len(node.as_string())

def set_end_col_offset(node, last_child=None):
    """Set the end_col_offset property by the as_string attribute.
    Uses the end column location of the last line, instead of the widest line.
    Need to do a custom postorder traversal to set end_col_offset property of 
    child nodes first, since it is sometimes unset in the last child.
    Postorder setting of children results in the assumption: if a node has the
    propert set, then all of its children are set.
    """
    if hasattr(node, 'end_lineno') and hasattr(node, 'end_col_offset'):
        if node.end_lineno and node.end_col_offset:
            return  # reduces runtime since properties already set.

    # Check: contradiction found. Revise NO_CHILDREN_TYPE list for correctness.
    assert not last_child or type(node) not in NO_CHILDREN_TYPE, '''ERROR:️ {} 
        node in NO_CHILDREN_TYPE has children ({}). Suggest: remove it from the 
        list.Context:\n{}'''.format(node, last_child, node.as_string())

    if hasattr(last_child, 'end_col_offset'):  # Set by last child
        assert last_child.end_col_offset is not None, '''ERROR:️ last child 
            end_col_offset should not be None if used to set others. 
            Node {}.'''.format(last_child)
        node.end_col_offset = last_child.end_col_offset
    # Set by string of node or last_child. May not have child.
    else:
        # Recall: children set first in postorder traversal.
        # Should this always set by string, is there another way?
        set_end_col_offset_by_string(node, last_child)

def _get_last_child(node):
    """Returns the last child node, or None.
    """
    if node.last_child():
        # logging.debug('\n node: {}. last_child: {}'.format(node, node.last_child()))
        return node.last_child()
    else:
        # Some nodes' last_child() attribute not set, e.g. astroid.Arguments
        # Get the first child, from the generator, and use its col_offset
        skip_to_last_child = None  # save a reference to last child for later.
        for skip_to_last_child in node.get_children():  # generator.
            pass  # skip to last
        return skip_to_last_child  # node, or None.

# Define the functions to transform the nodes.
# These functions are registered to their respective node type with the
# register_transform function.
# Mutates the nodes, adding the properties: `end_lineno`, `end_col_offset`.
def set_general(node):
    """General function called by many of the other transform functions.
    Populate ending locations for astroid node."""
    last_child = _get_last_child(node)
    set_end_lineno(node, last_child)
    set_end_col_offset(node, last_child)

def set_without_children(node):
    """Populate ending locations for nodes that are guaranteed to never have
    children. E.g. Const.
    """
    last_child = _get_last_child(node)
    set_end_lineno(node, last_child)
    set_end_col_offset_by_string(node, last_child)
