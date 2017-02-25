import ast
from _ast import *
import astroid.inference
import astroid
from astroid.node_classes import *
from typing import Tuple, List, Dict, Set, TupleMeta
from astroid.transforms import TransformVisitor

class NoType:
    pass

def set_const_type_constraints(node):
    """Populate type constraints for astroid nodes num/str/bool/None/bytes."""
    node.type_constraints = type(node.value)


def set_tuple_type_constraints(node):
    # node_types contains types of elements inside tuple.
    node.type_constraints = Tuple[tuple(x.type_constraints for x in node.elts)]


def set_list_type_constraints(node):
    # node_types contains types of elements inside list.
    node_types = {node_child.type_constraints for node_child in node.elts}
    # If list has more than one type, just set node.type_constraints to List.
    # If list has only one type T, set the node.type_constraints to be List[T].
    if len(node_types) == 1:
        # node_types.pop() returns the only element in the set, which is a
        # type object.
        node.type_constraints = List[node_types.pop()]
    else:
        node.type_constraints = List


def set_dict_type_constraints(node):
    # node_types contains types of elements inside Dict.
    key_types = {key.type_constraints for key, _ in node.items}
    value_types = {value.type_constraints for _, value in node.items}

    # If all the keys have the same type and all the values have the same type,
    # set the type constraint to a Dict of the two types.
    # Else, just use the general Dict type.
    if len(key_types) == 1 and len(value_types) == 1:
        node.type_constraints = Dict[key_types.pop(), value_types.pop()]
    else:
        node.type_constraints = Dict


def set_binop_type_constraints(node):
    ruled_type = helper_rules_binop(node.left, node.right, node.op)
    if len(ruled_type) == 1:
        node.type_constraints = ruled_type[0]
    else:
        raise ValueError('Different types of operands found, binop node %s'
                         'might have a type error.' % node)


def helper_rules_binop(par1, par2, operator):
    operand1 = par1.type_constraints
    operand2 = par2.type_constraints
    types = [] # result
    # checking if the types could possible be List/Tuple
    left_type = helper_list_tuple_detection(operand1)
    right_type = helper_list_tuple_detection(operand2)

    if operator == '+':
        if operand1 == float and operand2 == int:
            types.append(float)
        elif operand1 == int and operand2 == float:
            types.append(float)
        elif operand1 == int and operand2 == int:
            types.append(int)
        elif operand1 == float and operand2 == float:
            types.append(float)
        elif operand1 == str and operand2 == str:
            types.append(str)
        elif left_type == 1 and right_type == 1: # Both List
            if operand1 == operand2:
                types.append(operand1)
            else:
                types.append(List)
        elif left_type == 0 and right_type == 0: # Both Tuple
            types.append(Tuple[tuple(operand1.__tuple_params__ +
                                     operand2.__tuple_params__)])

    elif operator == '-':
        if operand1 == float and operand2 == int:
            types.append(float)
        elif operand1 == int and operand2 == float:
            types.append(float)
        elif operand1 == int and operand2 == int:
            types.append(int)
        elif operand1 == float and operand2 == float:
            types.append(float)

    elif operator == '*':
        if operand1 == float and operand2 == int:
            types.append(float)
        elif operand1 == int and operand2 == float:
            types.append(float)
        elif operand1 == int and operand2 == int:
            types.append(int)
        elif operand1 == float and operand2 == float:
            types.append(float)
        elif operand1 == int and operand2 == str:
            types.append(str)
        elif operand1 == str and operand2 == int:
            types.append(str)
        elif operand1 == int and right_type == 1:
            types.append(operand2)
        elif left_type == 1 and operand2 == int:
            types.append(operand1)
        elif operand1 == int and operand2 == List:
            types.append(List)
        elif operand1 == List and operand2 == int:
            types.append(List)
        elif operand1 == int and right_type == 0:
            types.append(Tuple[tuple(operand2.__tuple_params__ *
                                     par1.value)])
        elif left_type == 0 and operand2 == int:
            types.append(Tuple[tuple(operand1.__tuple_params__ *
                                     par2.value)])

    elif operator == '**' or operator == '%' or operator == '//':
        if operand1 == int and operand2 == int:
            types.append(int)
        elif operand1 == int and operand2 == float:
            types.append(float)
        elif operand1 == float and operand2 == int:
            types.append(float)
        elif operand1 == float and operand2 == float:
            types.append(float)

    elif operator == '/':
        if operand1 == int and operand2 == int:
            if par1.value % par2.value == 0:
                types.append(int)
            else:
                types.append(float)
        elif operand1 == int and operand2 == float:
            types.append(float)
        elif operand1 == float and operand2 == int:
            types.append(float)
        elif operand1 == float and operand2 == float:
            types.append(float)

    elif operator == '+=':
        if operand1 == int and operand2 == int:
            types.append(int)

    return types


def helper_list_tuple_detection(typeConstraints):
    result = -1
    if hasattr(typeConstraints, '__origin__'):
        if typeConstraints.__origin__ == List:
            result = 1
    elif hasattr(typeConstraints, '__class__'):
        if typeConstraints.__class__ == TupleMeta:
            result = 0
    return result


def set_unaryop_type_constraints(node):
    node.type_constraints = node.operand.type_constraints


def set_subscript_type_constraints(node):
    """Subscript nodes have 2 astroid_fields: slice and value, node.slice
    refers to a Name node and node.value refers to a Index node. In order to
    set the type_constraints for the Subscript node, we need to find what
    this node is referring to.

    Consider this code:
    list_example = [1, 2, 3, 'e']
    selected_element = list_example[2]

    After parsing and visiting, we'll have a Subscript Node. No valuable
    information can be found within its 2 attributes. We can use
    node.slice.value.value to find its corresponding index(int value),
    and for the original node that is subscript on(list_example in this
    case), we can use the lookup() function to find the module, then search
    for the list node with node.value.name... which is quite complex.
    Instead, by using node.infer(), we get the node at the corresponding
    index, and node.type_constraints can be recursively set by next(
    node.infer()).type_constraints.
    """
    inferred = next(node.infer())
    if hasattr(inferred, 'type_constraints'):
        node.type_constraints = next(node.infer()).type_constraints
    else:
        # Usually for sliced string that does not have the attribute
        # type_constraints. Consider the list l = ['aaa', 'bbb'], here we
        # would have 3 nodes that transform visitor had visited, l node and
        # 2 str node: 'aaa', 'bbb'.
        # However, if l[0][1] was accessed, it would not have
        # type_constraints at all, so I set the type_constraints below in
        # advance.
        if isinstance(inferred, Const):
            set_const_type_constraints(inferred)
            node.type_constraints = inferred.type_constraints


# TODO: Add check in the set_compare_type_constraints as in BinOp.
def set_compare_type_constraints(node):
    """Compare operators includes:
    '<', '>', '==', '>=', '<=', '<>', '!=', 'is' ['not'], ['not'] 'in' """
    node.type_constraints = bool


def set_boolop_type_constraints(node):
    """Boolean operators includes: 'and', 'or'
    Logic of Boolean Operations:
    x or y --> if x is false, then y, else x
    x and y --> if x is false, then x, else y
    """
    if node.op == 'or':
        if not node.values[0]:
            node.type_constraints = node.values[1].type_constraints
        else:
            node.type_constraints = node.values[0].type_constraints
    elif node.op == 'and':
        if not node.values[0]:
            node.type_constraints = node.values[0].type_constraints
        else:
            node.type_constraints = node.values[1].type_constraints


def set_expr_type_constraints(node):
    """Expr nodes take the value of their child
    """
    node.type_constraints = node.value.type_constraints


def set_assign_type_constraints(node):
    first_target = node.targets[0]
    node.type_constraints = (NoType, {first_target.name: node.value.type_constraints})


def set_module_type_constraints(node):
    names = {k: NoType for k in node.globals.keys()}
    for s in node.body:
        if s.is_statement and isinstance(s.type_constraints, tuple) and len(s.type_constraints) > 1:
            for identifier, type_constraint in s.type_constraints[1].items():
                if identifier in names:
                    names[identifier] = type_constraint
    node.type_constraints = (NoType, names)


def register_type_constraints_setter():
    """Instantiate a visitor to transform the nodes.
    Register the transform functions on an instance of TransformVisitor.
    """
    type_visitor = TransformVisitor()
    type_visitor.register_transform(astroid.Const, set_const_type_constraints)
    type_visitor.register_transform(astroid.Tuple, set_tuple_type_constraints)
    type_visitor.register_transform(astroid.List, set_list_type_constraints)
    type_visitor.register_transform(astroid.Dict, set_dict_type_constraints)
    type_visitor.register_transform(astroid.BinOp, set_binop_type_constraints)
    type_visitor.register_transform(astroid.UnaryOp,
                                    set_unaryop_type_constraints)
    type_visitor.register_transform(astroid.Subscript,
                                    set_subscript_type_constraints)
    type_visitor.register_transform(astroid.Compare,
                                    set_compare_type_constraints)
    type_visitor.register_transform(astroid.BoolOp,
                                    set_boolop_type_constraints)
    type_visitor.register_transform(astroid.Expr,
                                    set_expr_type_constraints)
    type_visitor.register_transform(astroid.Assign,
                                    set_assign_type_constraints)
    type_visitor.register_transform(astroid.Module,
                                    set_module_type_constraints)
    return type_visitor
