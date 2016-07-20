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
    """
    node.end_lineno = node.lineno

def _set_end_lineno(node):
    """Transform the property in-place.
    Testing with simple, single-line things for now.
    Goal is to work on various multi-line nodes, with complicated nesting.
    'tolineno' is set correctly on everything, by asteroid.
    """
    # Guard. 
    if node.tolineno is None:
        # TODO: write new code to gracefully handle, if this is ever reached.
        logging.error("⛔ lineno is None at node: {}".format(node))
        sys.exit(1)
    else:
        node.end_lineno = node.tolineno

def _set_end_col_offset_by_string_old(node):
    """Set the end_col_offset property by the as_string attribute.
    Uses the end column location of the last line, instead of the widest line.
    """
    
    # Get the widest line in the source code.
    lines = [line for line in node.as_string().split('\n')]
    max_width_line = max(lines, key=len)
    max_width = len(max_width_line)
    # Note: node.col_offset could be 'None'
    node.end_col_offset = (node.col_offset or 0) + max_width



def _set_end_col_offset_by_string(node):
    """Set the end_col_offset property by the as_string attribute.
    Uses the end column location of the last line, instead of the widest line.
    Need to do a custom postorder traversal to set end_col_offset property of 
    child nodes first, since it is sometimes unset in the last child.
    Postorder setting of children results in the assumption: if a node has the
    propert set, then all of its children are set.
    """

    # Compare with "None" since value could be "0", which is falsey.
    # Returning a.s.a.p. reduces the runtime (considerably?).
    if node.end_lineno is not None and node.end_col_offset is not None:
        return  # since properties are already set.

    # Doing this first makes it a postorder traversal.
    for child in node.get_children():  # get_children() returns a generator.
        _set_end_col_offset_by_string(child)

    node_as_string = str(node)
    node_name = node_as_string[ : node_as_string.find('(')]
    # print('node: ', node_name)

    #❕TODO: set up the below to work with postorder traversal, setting all
    # child properties, calling the different transform functions by node
    # type in nodes.. nodes[node_name]['function']






    


    # Temporary:    
    # print('props: ', dir(node))
    last_child_end = node.last_child().end_col_offset
    if last_child_end is None:
        logging.error("⛔ ERROR:️ last child's end_col_offset property is None.")
        # sys.exit(1)
        raise Exception('''⛔ last child's end_col_offset property is None.''')
        # TODO: get the type of astroid node (Const?, Expr?, ...)
        # and calculate its 

    print('last: ', node.last_child().end_col_offset)
    node.end_col_offset = node.last_child().end_col_offset
    




def _set_end_col_offset_by_value(node):
    """Set the end_col_offset property by the value attribute.
    """
    # Guard: should have .value property
    if 'value' not in dir(node):
        raise Exception('''⛔️ node must have the .value property.''')
        sys.exit(1)

    # Guard: something with .value shouldn't have children. Use a different
    # function instead of _set_end_col_offset_by_value.
    for child in node.get_children():  # get_children() returns a generator.
        raise Exception('''⛔ _set_end_col_offset_by_value function 
                        should not be called if has children.''')
        sys.exit(1)
    node.end_col_offset = node.col_offset + len(str(node.value))


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
    _set_end_col_offset_by_string(node)

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

def set_binop(node):
    """Populate ending locations for node: astroid.BinOp"""
    set_general(node)

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

def set_const(node):
    """Populate ending locations for node: astroid.Const
    Note: only Const node has .value property.
    Examples include: ints, None, True, False.
    Always true: Const is always 1 line.
    """
    _set_end_lineno(node)
    _set_end_col_offset_by_value(node)

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
    set_general(node)

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







# Data structure to control the transform functions bound to each node type.
# Some nodes will share general transform functions.
# Sometimes postorder traversals are done on subtrees of nodes, and we use the
# binding of node string to transform function to dynamically set attributes
# within the subtree.
# Use like: 
    # x = 'BinOp'
    # nodes[x][function]
################################################################################
nodes = {
'Arguments': {'function': set_arguments,
            'node': astroid.Arguments,
            'string': 'Arguments'},
'Assert': {'function': set_assert,
            'node': astroid.Assert,
            'string': 'Assert'},
'Assign': {'function': set_assign,
            'node': astroid.Assign,
            'string': 'Assign'},
'AssignAttr': {'function': set_assignattr,
            'node': astroid.AssignAttr,
            'string': 'AssignAttr'},
'AssignName': {'function': set_assignname,
            'node': astroid.AssignName,
            'string': 'AssignName'},
'AsyncFor': {'function': set_asyncfor,
            'node': astroid.AsyncFor,
            'string': 'AsyncFor'},
'AsyncFunctionDef': {'function': set_asyncfunctiondef,
            'node': astroid.AsyncFunctionDef,
            'string': 'AsyncFunctionDef'},
'AsyncWith': {'function': set_asyncwith,
            'node': astroid.AsyncWith,
            'string': 'AsyncWith'},
'Attribute': {'function': set_attribute,
            'node': astroid.Attribute,
            'string': 'Attribute'},
'AugAssign': {'function': set_augassign,
            'node': astroid.AugAssign,
            'string': 'AugAssign'},
'Await': {'function': set_await,
            'node': astroid.Await,
            'string': 'Await'},
'BinOp': {'function': set_binop,
            'node': astroid.BinOp,
            'string': 'BinOp'},
'BoolOp': {'function': set_boolop,
            'node': astroid.BoolOp,
            'string': 'BoolOp'},
'Break': {'function': set_break,
            'node': astroid.Break,
            'string': 'Break'},
'Call': {'function': set_call,
            'node': astroid.Call,
            'string': 'Call'},
'ClassDef': {'function': set_classdef,
            'node': astroid.ClassDef,
            'string': 'ClassDef'},
'Compare': {'function': set_compare,
            'node': astroid.Compare,
            'string': 'Compare'},
'Comprehension': {'function': set_comprehension,
            'node': astroid.Comprehension,
            'string': 'Comprehension'},
'Const': {'function': set_const,
            'node': astroid.Const,
            'string': 'Const'},
'Continue': {'function': set_continue,
            'node': astroid.Continue,
            'string': 'Continue'},
'Decorators': {'function': set_decorators,
            'node': astroid.Decorators,
            'string': 'Decorators'},
'DelAttr': {'function': set_delattr,
            'node': astroid.DelAttr,
            'string': 'DelAttr'},
'DelName': {'function': set_delname,
            'node': astroid.DelName,
            'string': 'DelName'},
'Delete': {'function': set_delete,
            'node': astroid.Delete,
            'string': 'Delete'},
'Dict': {'function': set_dict,
            'node': astroid.Dict,
            'string': 'Dict'},
'DictComp': {'function': set_dictcomp,
            'node': astroid.DictComp,
            'string': 'DictComp'},
'DictUnpack': {'function': set_dictunpack,
            'node': astroid.DictUnpack,
            'string': 'DictUnpack'},
'Ellipsis': {'function': set_ellipsis,
            'node': astroid.Ellipsis,
            'string': 'Ellipsis'},
'EmptyNode': {'function': set_emptynode,
            'node': astroid.EmptyNode,
            'string': 'EmptyNode'},
'ExceptHandler': {'function': set_excepthandler,
            'node': astroid.ExceptHandler,
            'string': 'ExceptHandler'},
'Exec': {'function': set_exec,
            'node': astroid.Exec,
            'string': 'Exec'},
'Expr': {'function': set_expr,
            'node': astroid.Expr,
            'string': 'Expr'},
'ExtSlice': {'function': set_extslice,
            'node': astroid.ExtSlice,
            'string': 'ExtSlice'},
'For': {'function': set_for,
            'node': astroid.For,
            'string': 'For'},
'FunctionDef': {'function': set_functiondef,
            'node': astroid.FunctionDef,
            'string': 'FunctionDef'},
'GeneratorExp': {'function': set_generatorexp,
            'node': astroid.GeneratorExp,
            'string': 'GeneratorExp'},
'Global': {'function': set_global,
            'node': astroid.Global,
            'string': 'Global'},
'If': {'function': set_if,
            'node': astroid.If,
            'string': 'If'},
'IfExp': {'function': set_ifexp,
            'node': astroid.IfExp,
            'string': 'IfExp'},
'Import': {'function': set_import,
            'node': astroid.Import,
            'string': 'Import'},
'ImportFrom': {'function': set_importfrom,
            'node': astroid.ImportFrom,
            'string': 'ImportFrom'},
'Index': {'function': set_index,
            'node': astroid.Index,
            'string': 'Index'},
'Keyword': {'function': set_keyword,
            'node': astroid.Keyword,
            'string': 'Keyword'},
'Lambda': {'function': set_lambda,
            'node': astroid.Lambda,
            'string': 'Lambda'},
'List': {'function': set_list,
            'node': astroid.List,
            'string': 'List'},
'ListComp': {'function': set_listcomp,
            'node': astroid.ListComp,
            'string': 'ListComp'},
'Module': {'function': set_module,
            'node': astroid.Module,
            'string': 'Module'},
'Name': {'function': set_name,
            'node': astroid.Name,
            'string': 'Name'},
'Nonlocal': {'function': set_nonlocal,
            'node': astroid.Nonlocal,
            'string': 'Nonlocal'},
'Pass': {'function': set_pass,
            'node': astroid.Pass,
            'string': 'Pass'},
'Print': {'function': set_print,
            'node': astroid.Print,
            'string': 'Print'},
'Raise': {'function': set_raise,
            'node': astroid.Raise,
            'string': 'Raise'},
'Repr': {'function': set_repr,
            'node': astroid.Repr,
            'string': 'Repr'},
'Return': {'function': set_return,
            'node': astroid.Return,
            'string': 'Return'},
'Set': {'function': set_set,
            'node': astroid.Set,
            'string': 'Set'},
'SetComp': {'function': set_setcomp,
            'node': astroid.SetComp,
            'string': 'SetComp'},
'Slice': {'function': set_slice,
            'node': astroid.Slice,
            'string': 'Slice'},
'Starred': {'function': set_starred,
            'node': astroid.Starred,
            'string': 'Starred'},
'Subscript': {'function': set_subscript,
            'node': astroid.Subscript,
            'string': 'Subscript'},
'TryExcept': {'function': set_tryexcept,
            'node': astroid.TryExcept,
            'string': 'TryExcept'},
'TryFinally': {'function': set_tryfinally,
            'node': astroid.TryFinally,
            'string': 'TryFinally'},
'Tuple': {'function': set_tuple,
            'node': astroid.Tuple,
            'string': 'Tuple'},
'UnaryOp': {'function': set_unaryop,
            'node': astroid.UnaryOp,
            'string': 'UnaryOp'},
'While': {'function': set_while,
            'node': astroid.While,
            'string': 'While'},
'With': {'function': set_with,
            'node': astroid.With,
            'string': 'With'},
'Yield': {'function': set_yield,
            'node': astroid.Yield,
            'string': 'Yield'},
'YieldFrom': {'function': set_yieldfrom,
            'node': astroid.YieldFrom,
            'string': 'YieldFrom'}
}    




