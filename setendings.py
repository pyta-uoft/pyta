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
    # Guard. 
    if node.tolineno is None:
        # TODO: write new code to gracefully handle, if this is ever reached.
        raise Exception('''ERROR:️ lineno is None at node:''', node, 
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

    # if possible, set the end_col_offset by that of the last child
    if node.last_child():
        _set_by_last_child(node, node.last_child())
    # Arrgghh astroid.Arguments cannot rely on last_child() being set properly.
    elif type(node) is astroid.Arguments:
        last_child = None
        for last_child in node.get_children():  # get_children() returns a generator
            pass  # skip to last
        print('last item in Arguments:', last_child)
        _set_by_last_child(node, last_child)
    # No children. Postorder traversal sets these children first.
    else:
        # print(type(node) in NO_CHILDREN)
        print('no children: {}'.format(node))
        _set_end_col_offset_by_string(node)

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

#######

def set_arguments(node):
    """Populate ending locations for node: astroid.Arguments"""
    set_general(node)

def set_assert(node):
    """Populate ending locations for node: astroid.Assert"""
    set_general(node)

def set_assign(node):
    """Populate ending locations for node: astroid.Assign"""
    set_general(node)

def set_assignattr(node):
    """Populate ending locations for node: astroid.AssignAttr"""
    set_general(node)

def set_assignname(node):
    """Populate ending locations for node: astroid.AssignName"""
    set_general(node)

def set_asyncfor(node):
    """Populate ending locations for node: astroid.AsyncFor"""
    set_general(node)

def set_asyncfunctiondef(node):
    """Populate ending locations for node: astroid.AsyncFunctionDef"""
    set_general(node)

def set_asyncwith(node):
    """Populate ending locations for node: astroid.AsyncWith"""
    set_general(node)

def set_attribute(node):
    """Populate ending locations for node: astroid.Attribute"""
    set_general(node)

def set_augassign(node):
    """Populate ending locations for node: astroid.AugAssign"""
    set_general(node)

def set_await(node):
    """Populate ending locations for node: astroid.Await"""
    set_general(node)

# def set_binop(node):
#     """Populate ending locations for node: astroid.BinOp"""
#     set_general(node)

def set_boolop(node):
    """Populate ending locations for node: astroid.BoolOp"""
    set_general(node)

def set_break(node):
    """Populate ending locations for node: astroid.Break"""
    set_general(node)

def set_call(node):
    """Populate ending locations for node: astroid.Call"""
    set_general(node)

def set_classdef(node):
    """Populate ending locations for node: astroid.ClassDef"""
    set_general(node)

def set_compare(node):
    """Populate ending locations for node: astroid.Compare"""
    set_general(node)

def set_comprehension(node):
    """Populate ending locations for node: astroid.Comprehension"""
    set_general(node)

# def set_const(node):
#     """Populate ending locations for node: astroid.Const
#     Note: only Const node has .value property.
#     Examples include: ints, None, True, False.
#     Always true: Const is always 1 line.
#     """
#     _set_end_lineno(node)
#     _set_child_end_col_offset_by_value(node)

def set_continue(node):
    """Populate ending locations for node: astroid.Continue"""
    set_general(node)

def set_decorators(node):
    """Populate ending locations for node: astroid.Decorators"""
    set_general(node)

def set_delattr(node):
    """Populate ending locations for node: astroid.DelAttr"""
    set_general(node)

def set_delname(node):
    """Populate ending locations for node: astroid.DelName"""
    set_general(node)

def set_delete(node):
    """Populate ending locations for node: astroid.Delete"""
    set_general(node)

def set_dict(node):
    """Populate ending locations for node: astroid.Dict"""
    set_general(node)

def set_dictcomp(node):
    """Populate ending locations for node: astroid.DictComp"""
    set_general(node)

def set_dictunpack(node):
    """Populate ending locations for node: astroid.DictUnpack"""
    set_general(node)

def set_ellipsis(node):
    """Populate ending locations for node: astroid.Ellipsis"""
    set_general(node)

def set_emptynode(node):
    """Populate ending locations for node: astroid.EmptyNode"""
    set_general(node)

def set_excepthandler(node):
    """Populate ending locations for node: astroid.ExceptHandler"""
    set_general(node)

def set_exec(node):
    """Populate ending locations for node: astroid.Exec"""
    set_general(node)

def set_expr(node):
    """Populate ending locations for node: astroid.Expr"""
    set_general(node)

def set_extslice(node):
    """Populate ending locations for node: astroid.ExtSlice"""
    set_general(node)

def set_for(node):
    """Populate ending locations for node: astroid.For"""
    set_general(node)

def set_functiondef(node):
    """Populate ending locations for node: astroid.FunctionDef"""
    set_general(node)

def set_generatorexp(node):
    """Populate ending locations for node: astroid.GeneratorExp"""
    set_general(node)

def set_global(node):
    """Populate ending locations for node: astroid.Global"""
    set_general(node)

def set_if(node):
    """Populate ending locations for node: astroid.If"""
    set_general(node)

def set_ifexp(node):
    """Populate ending locations for node: astroid.IfExp"""
    set_general(node)

def set_import(node):
    """Populate ending locations for node: astroid.Import"""
    set_general(node)

def set_importfrom(node):
    """Populate ending locations for node: astroid.ImportFrom"""
    set_general(node)

def set_index(node):
    """Populate ending locations for node: astroid.Index"""
    set_general(node)

def set_keyword(node):
    """Populate ending locations for node: astroid.Keyword"""
    set_general(node)

def set_lambda(node):
    """Populate ending locations for node: astroid.Lambda"""
    set_general(node)

def set_list(node):
    """Populate ending locations for node: astroid.List"""
    set_general(node)

def set_listcomp(node):
    """Populate ending locations for node: astroid.ListComp"""
    set_general(node)

def set_module(node):
    """Populate ending locations for node: astroid.Module"""
    set_general(node)

def set_name(node):
    """Populate ending locations for node: astroid.Name"""
    set_general(node)

def set_nonlocal(node):
    """Populate ending locations for node: astroid.Nonlocal"""
    set_general(node)

def set_pass(node):
    """Populate ending locations for node: astroid.Pass"""
    # set_general(node)
    _set_end_lineno(node)
    node.end_col_offset = node.col_offset + 4  # "pass" has constant length

def set_print(node):
    """Populate ending locations for node: astroid.Print"""
    set_general(node)

def set_raise(node):
    """Populate ending locations for node: astroid.Raise"""
    set_general(node)

def set_repr(node):
    """Populate ending locations for node: astroid.Repr"""
    set_general(node)

def set_return(node):
    """Populate ending locations for node: astroid.Return"""
    set_general(node)

def set_set(node):
    """Populate ending locations for node: astroid.Set"""
    set_general(node)

def set_setcomp(node):
    """Populate ending locations for node: astroid.SetComp"""
    set_general(node)

def set_slice(node):
    """Populate ending locations for node: astroid.Slice"""
    set_general(node)

def set_starred(node):
    """Populate ending locations for node: astroid.Starred"""
    set_general(node)

def set_subscript(node):
    """Populate ending locations for node: astroid.Subscript"""
    set_general(node)

def set_tryexcept(node):
    """Populate ending locations for node: astroid.TryExcept"""
    set_general(node)

def set_tryfinally(node):
    """Populate ending locations for node: astroid.TryFinally"""
    set_general(node)

def set_tuple(node):
    """Populate ending locations for node: astroid.Tuple"""
    set_general(node)

def set_unaryop(node):
    """Populate ending locations for node: astroid.UnaryOp"""
    set_general(node)

def set_while(node):
    """Populate ending locations for node: astroid.While"""
    set_general(node)

def set_with(node):
    """Populate ending locations for node: astroid.With"""
    set_general(node)

def set_yield(node):
    """Populate ending locations for node: astroid.Yield"""
    set_general(node)

def set_yieldfrom(node):
    """Populate ending locations for node: astroid.YieldFrom"""
    set_general(node)


