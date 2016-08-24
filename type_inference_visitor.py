import warnings
from typing import Tuple, List, Dict, Set


def set_const_type_constraints(node):
    """Populate type constraints for astroid nodes num/str/bool/None/bytes."""
    node.type_constraints = type(node.value)


def set_tuple_type_constraints(node):
    # node_types contains types of elements inside tuple.
    node_elements_types = [x.type_constraints for x in node.elts]
    node.type_constraints = Tuple[tuple(node_elements_types)]


def set_list_type_constraints(node):
    # node_types contains types of elements inside list.
    node_types = set()
    for node_child in node.elts:
        node_types.add(node_child.type_constraints)

    # if list has more than one types, just set node.type_constraints to
    # list, if list has only 1 types, set the node.type_constraints to be
    # List of that type.
    if len(node_types) == 1:
        # node_types.pop() returns the only element in the set, which is a
        # type object.
        node.type_constraints = List[node_types.pop()]
    else:
        node.type_constraints = List


def set_dict_type_constraints(node):
    # node_types contains types of elements inside Dict.
    key_types = set()
    value_types = set()
    for key, value in node.items:
        key_types.add(key.type_constraints)
        value_types.add(value.type_constraints)

    # if all the keys have the same type, and all the values have the same
    # type, return the node.type_constraints with the 2 types, else,
    # just return the general Dict type.
    if len(key_types) == 1 and len(value_types) == 1:
        node.type_constraints = Dict[key_types.pop(), value_types.pop()]
    else:
        node.type_constraints = Dict


def set_binop_type_constraints(node):
    # recursive
    left_operand = node.left.type_constraints
    right_operand = node.right.type_constraints

    node.type_constraints = left_operand
    if ((right_operand == int and node.type_constraints == float) or
        (right_operand == float and node.type_constraints == int)):
        node.type_constraints = float
    elif right_operand == left_operand:
        node.type_constraints = right_operand
    else:
        warnings.warn('Different types of operands found, binop node %s'
                      'might have a type error.' % node)


def set_unaryop_type_constraints(node):
    # recursive
    node.type_constraints = node.operand.type_constraints
