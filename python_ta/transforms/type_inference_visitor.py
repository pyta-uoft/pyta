import astroid
import astroid.node_classes
from typing import Tuple, List, Dict, Set, TupleMeta
from astroid.transforms import TransformVisitor


def set_const_type_constraints(node):
    """Populate type constraints for astroid nodes num/str/bool/None/bytes."""
    node.type_constraints = type(node.value)


def set_tuple_type_constraints(node):
    # node_types contains types of elements inside tuple.
    node.type_constraints = Tuple[tuple(x.type_constraints for x in node.elts)]

# subscript node

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


def helper_rules(operand1, operand2, operator):

    # checking if the types could possible be List/Tuple
    left_type = -1
    right_type = -1

    if hasattr(operand1, '__origin__'):
        if operand1.__origin__ == List:
            left_type = 1 # 1 for List 0 for Tuple.
    elif hasattr(operand1, '__class__'):
        if operand1.__class__ == TupleMeta:
            left_type = 0

    if hasattr(operand2, '__origin__'):
        if operand2.__origin__ == List:
            right_type = 1
    elif hasattr(operand2, '__class__'):
        if operand2.__class__ == TupleMeta:
            right_type = 0

    if operator == '+':
        if operand1 == float and operand2 == int:
            return [float]
        elif operand1 == int and operand2 == float:
            return [float]
        elif operand1 == int and operand2 == int:
            return [int]
        elif operand1 == float and operand2 == float:
            return [float]
        elif operand1 == str and operand2 == str:
            return [str]
        elif left_type == 1 and right_type == 1: # Both List
            return [List, List]
        elif left_type == 0 and right_type == 0: # Both Tuple
            return [Tuple, Tuple]

    elif operator == '-':
        if operand1 == float and operand2 == int:
            return [float]
        elif operand1 == int and operand2 == float:
            return [float]
        elif operand1 == int and operand2 == int:
            return [int]
        elif operand1 == float and operand2 == float:
            return [float]

    elif operator == '*':
        if operand1 == float and operand2 == int:
            return [float]
        elif operand1 == int and operand2 == float:
            return [float]
        elif operand1 == int and operand2 == int:
            return [int]
        elif operand1 == float and operand2 == float:
            return [float]
        elif operand1 == int and operand2 == str:
            return [str]
        elif operand1 == str and operand2 == int:
            return [str]
        elif operand1 == int and right_type == 1:
            return [int, List]
        elif left_type == 1 and operand2 == int:
            return [List, int]
        elif operand1 == int and operand2 == List:
            return [List]
        elif operand1 == List and operand2 == int:
            return [List]
        elif operand1 == int and right_type == 0:
            return [int, Tuple]
        elif left_type == 0 and operand2 == int:
            return [Tuple, int]

    else:
        return []


def set_binop_type_constraints(node):
    left_type = node.left.type_constraints
    right_type = node.right.type_constraints

    ruled_type = helper_rules(left_type, right_type, node.op)

    if len(ruled_type) == 1:
        node.type_constraints = ruled_type[0]
    elif len(ruled_type) == 2:
        # both Tuple
        if ruled_type == [Tuple, Tuple]:
            all_elts = node.left.elts + node.right.elts
            node.type_constraints = Tuple[tuple(x.type_constraints for x in
                                                all_elts)]
        # both List
        elif ruled_type == [List, List]:
            if left_type == right_type:
                node.type_constraints = left_type
            else:
                node.type_constraints = List
        # multiply an int n to a list l is concatenating n-1 times l to the
        # original list l.
        elif ruled_type == [List, int]:
            node.type_constraints = left_type
        elif ruled_type == [int, List]:
            node.type_constraints = right_type
        # multiply an int n to a tuple t is concatenating n-1 times t to the
        # original tuple t.
        elif ruled_type == [Tuple, int]:
            node.type_constraints = Tuple[tuple(x.type_constraints for x in
                                        node.left.elts * node.right.value)]
        elif ruled_type == [int, Tuple]:
            node.type_constraints = Tuple[tuple(x.type_constraints for x in
                                        node.right.elts * node.left.value)]
    else:
        raise ValueError('Different types of operands found, binop node %s'
                         'might have a type error.' % node)


def set_unaryop_type_constraints(node):
    node.type_constraints = node.operand.type_constraints


def register_type_constraints_setter():
    """Instantiate a visitor to transform the nodes.
    Register the transform functions on an instance of TransformVisitor.
    """
    type_visitor = TransformVisitor()
    type_visitor.register_transform(astroid.Const, set_const_type_constraints)
    type_visitor.register_transform(astroid.Tuple, set_tuple_type_constraints)
    type_visitor.register_transform(astroid.List, set_list_type_constraints)
    type_visitor.register_transform(astroid.Dict, set_dict_type_constraints)
    type_visitor.register_transform(astroid.UnaryOp,
                                    set_unaryop_type_constraints)
    type_visitor.register_transform(astroid.BinOp, set_binop_type_constraints)
    return type_visitor
