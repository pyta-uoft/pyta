from astroid.transforms import TransformVisitor
import astroid
import warnings
from typing import Tuple, List, Dict


class TypeVisitor(TransformVisitor):

    def _visit(self, node):
        if hasattr(node, '_astroid_fields'):
            for field in node._astroid_fields:
                value = getattr(node, field)
                visited = self._visit_generic(value)
                setattr(node, field, visited)
        return self._transform(node)

    def _visit_generic(self, node):
        if isinstance(node, list):
            return [self._visit_generic(child) for child in node]
        elif isinstance(node, tuple):
            return tuple(self._visit_generic(child) for child in node)
        else:
            return self._visit(node)


def set_const_type_constraints(node):
    """Populate type constraints for astroid nodes num/str/bool/None/bytes."""
    node.type_constraints = node.value.__class__


def set_tuple_type_constraints(node):
    # node_types contains types of elements inside tuple.
    node_types = [node_child.type_constraints for node_child in node.elts]
    # Since tuple has only 2 elements, node.type_constraints will return
    # types of both elements.
    node.type_constraints = Tuple[node_types[0], node_types[1]]


def set_list_type_constraints(node):
    # node_types contains types of elements inside list.
    node_types = []
    for node_child in node.elts:
        if node_child.type_constraints not in node_types:
            node_types.append(node_child.type_constraints)

    # if list has more than one types, just set node.type_constraints to
    # list, if list has only 1 types, set the node.type_constraints to be
    # List of that type.
    if len(node_types) == 1:
        node.type_constraints = List[node_types[0]]
    else:
        node.type_constraints = List


def set_dict_type_constraints(node):
    # node_types contains types of elements inside Dict.
    key_types = []
    value_types = []
    for key, value in node.items:
        if key.type_constraints not in key_types:
            key_types.append(key.type_constraints)
        if value.type_constraints not in value_types:
            value_types.append(value.type_constraints)

    # if all the keys have the same type, and all the values have the same
    # type, return the node.type_constraints with the 2 types, else,
    # just return the general Dict type.
    if len(key_types) == 1 and len(value_types) == 1:
        node.type_constraints = Dict[key_types[0], value_types[0]]
    else:
        node.type_constraints = Dict


def set_binop_type_constraints(node):
    op = node.op
    left_operand = node.left.type_constraints
    right_operand = node.right.type_constraints

    node.type_constraints = left_operand
    if ((right_operand == int and node.type_constraints ==float) or
        (right_operand == float and node.type_constraints == int)):
        node.type_constraints = float
    elif right_operand==left_operand:
        node.type_constraints = right_operand
    else:
        warnings.warn('Different types of operands found, binop node %s'
                      'might have a type error.' % node)


def set_unaryop_type_constraints(node):
    op = node.op
    operand = node.operand.value
    node.type_constraints = type(operand)
