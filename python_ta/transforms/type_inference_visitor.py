import astroid
import astroid.node_classes
from typing import Tuple, List, Dict, Set
from astroid.transforms import TransformVisitor


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
    left_type = node.left.type_constraints
    right_type = node.right.type_constraints

    # '*' does not work for same type of operands such as str, list... etc
    if node.op != '*' and left_type == right_type:
        node.type_constraints = node.left.type_constraints

    # A list can be concatenate to another list using '+' operator
    elif node.op == '+' and \
            (isinstance(node.left, astroid.node_classes.List) and
                isinstance(node.right, astroid.node_classes.List)):
        node.type_constraints = List

    # A tuple can be concatenate to another tuple using '+' operator
    elif node.op == '+' and \
            (isinstance(node.left, astroid.node_classes.Tuple) and
                isinstance(node.right, astroid.node_classes.Tuple)):
        node.type_constraints = Tuple[tuple(x.type_constraints for x in
                                            node.left.elts + node.right.elts)]

    # operations between an integer and float should result a float
    elif ((right_type == int and left_type == float) or
        (right_type == float and left_type == int)):
        node.type_constraints = float

    elif right_type == int and left_type == int:
        node.type_constraints = int

    elif right_type == float and left_type == float:
        node.type_constraints = float

    # multiply an int n to a str s is concatenating n-1 times s to the
    # original string s.
    elif node.op == '*' and \
            ((right_type == int and left_type == str) or
            (right_type == str and left_type == int)):
        node.type_constraints = str

    # multiply an int n to a list l is concatenating n-1 times l to the
    # original list l.
    elif node.op == '*' and left_type == int and \
            isinstance(node.right, astroid.node_classes.List):
        node.type_constraints = right_type

    elif node.op == '*' and right_type == int and \
            isinstance(node.left, astroid.node_classes.List):
        node.type_constraints = left_type

    # multiply an int n to a tuple t is concatenating n-1 times t to the
    # original tuple t.
    elif node.op == '*' and left_type == int and \
            isinstance(node.right, astroid.node_classes.Tuple):
        node.type_constraints = Tuple[tuple(x.type_constraints for x in
                                            node.right.elts * node.left.value)]

    elif node.op == '*' and right_type == int and \
            isinstance(node.left, astroid.node_classes.Tuple):
        node.type_constraints = Tuple[tuple(x.type_constraints for x in
                                            node.left.elts * node.right.value)]

    # for all other invalid cases, raise an ValueError
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
