"""Helper module for ending_location_visitor.py
"""
from sys import exit
import astroid
import logging

# Set the log level (DEBUG, ERROR, ...), and message format.
logging.basicConfig(format='', level=logging.DEBUG)

# Helper functions to abstract common tasks. Global for now..
# these functions are associated to types in the transforms dictionary in the
# TransformVisitor class. The _transform method invokes the transform function
# on the nodes.
# TODO: Separate into Class? .. would need static methods.
################################################################################

def _set_end_lineno(node):
    """Transform the property in-place.
    Testing with simple, single-line things for now.
    Goal is to work on various multi-line nodes, with complicated nesting.
    'tolineno' is set correctly on everything, by asteroid.
    """

    # TODO: set this from the last child!!

    # Guard. 
    if node.tolineno is None:
        # TODO: write new code to gracefully handle, if this is ever reached.
        raise Exception('''ERROR:️ tolineno is None at node:''', node, 
                        node.as_string())
    else:
        node.end_lineno = node.tolineno

def _set_end_col_offset_by_string(node):
    """Nodes without children can get end_col_offset by length of string.
    Hopefully this works without problems.
    """
    NO_CHILDREN_TYPE = [astroid.Arguments, astroid.AssignName, astroid.Break, 
            astroid.Const, astroid.DelName, astroid.Ellipsis, astroid.Global, 
            astroid.Import, astroid.ImportFrom, astroid.List, astroid.Name, 
            astroid.Nonlocal, astroid.Pass, astroid.Yield]

    node_string = node.as_string()

    if type(node) not in NO_CHILDREN_TYPE:
        raise Exception('''ERROR:️ node not found in NO_CHILDREN list.''', node, 
                        node_string)

    # Guard: to use this approach, it shouldn't have children.
    for child in node.get_children():  # get_children() returns a generator.
        raise Exception('''ERROR:️ should not be called if has children.''', 
                        node, node_string)

    # Guard: should have .value property
    if not hasattr(node, 'as_string'):
        raise Exception('''ERROR:️ node must have the .as_string property.''', 
                        node, node_string)

    # _set_child_end_col_offset_by_value(node)
    node.end_col_offset = node.col_offset + len(node_string)

def _set_end_col_offset(node):
    """Set the end_col_offset property by the as_string attribute.
    Uses the end column location of the last line, instead of the widest line.
    Need to do a custom postorder traversal to set end_col_offset property of 
    child nodes first, since it is sometimes unset in the last child.
    Postorder setting of children results in the assumption: if a node has the
    propert set, then all of its children are set.
    """

    # Compare with "None" since value could be "0", which is falsey.
    # Returning a.s.a.p. reduces the runtime.
    # Some nodes dont have the attribute set yet.
    if hasattr(node, 'end_lineno') and hasattr(node, 'end_col_offset'):
        if node.end_lineno is not None and node.end_col_offset is not None:
            return  # since properties are already set.

    # Doing this first makes it a postorder traversal.
    for child in node.get_children():  # get_children() returns a generator.
        _set_end_col_offset(child)

    last_child = _get_last_child(node)

    # if possible, set the end_col_offset by that of the last child
    if last_child:
        # astroid.Arguments nodes dont have a 'lineno' or 'col_offset' property!
        # Note: there may be others out there!
        if type(node) is astroid.Arguments:
            node.col_offset = next(node.get_children()).col_offset

        alert_property_missing(last_child)
        _set_by_last_child(node, last_child)
    else:
        print('no children: {}'.format(node))
        alert_property_missing(node)
        _set_end_col_offset_by_string(node)

def _get_last_child(node):
    """Returns the last child, or if no children, returns None.
    """
    if node.last_child():
        return node.last_child()
    # Arrgghh astroid.Arguments dont have a last_child()!
    elif type(node) is astroid.Arguments:
        # Get the first child, from the generator, and use its col_offset
        last_child = None  # save a reference to last child for later.
        for last_child in node.get_children():  # get_children() returns a generator
            pass  # skip to last
        if last_child is None:
            raise Exception('''ERROR:️ last_child is None at node:''', node, 
                            node.as_string())
        return last_child
    else:
        return None

def _set_by_last_child(node, last_child_node):
    """Set end_col_offset by the value of the node's last child.
    """
    if hasattr(last_child_node, 'end_col_offset'):
        if last_child_node.end_col_offset is None:  # this shoulnt happen
            raise Exception("ERROR:️ last child's end_col_offset property is None.")
        node.end_col_offset = last_child_node.end_col_offset
    # Postorder sets children first!
    else:
        node.end_col_offset = last_child_node.col_offset + len(node.as_string())
        print('end_col_offset was set: ', node.end_col_offset)

def alert_property_missing(node):
    """Purpose: alert immediately if any properties are missing in any of the
    many different types of nodes. For example 'lineno' and 'col_offset' are
    originally missing in all astroid.Arguments nodes.
    TODO: Write new code to gracefully handle, if exceptions are ever raised.
    """
    if node.tolineno is None:
        raise Exception('''ERROR:️ tolineno is None at node:''', node, 
                        node.as_string())

    if node.fromlineno is None:
        raise Exception('''ERROR:️ fromlineno is None at node:''', node, 
                        node.as_string())

    if node.col_offset is None:
        raise Exception('''ERROR:️ col_offset is None at node:''', node, 
                        node.as_string())



# TODO: maybe separate the following concerns into different files.
# Define the functions to transform the nodes.
# These functions are registered to their respective node type with the
# register_transform function.
# Mutate the nodes, adding the properties: `end_lineno`, `end_col_offset`.
################################################################################
def set_general(node):
    """General function called by many of the other transform functions.
    Populate ending locations for astroid node."""
    _set_end_lineno(node)
    _set_end_col_offset(node)

