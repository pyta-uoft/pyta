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

    # def _visit(self, node):
    #     # If node is an instance of List/Tuple/Dict, instead of breaking
    #     # down to smaller pieces of node such as const nodes, keep the
    #     # bigger piece and directly use an transform function on it.
    #     if isinstance(node, astroid.List) or isinstance(node, astroid.Tuple)\
    #             or isinstance(node, astroid.Dict):
    #         return self._transform(node)
    #     if hasattr(node, '_astroid_fields'):
    #         for field in node._astroid_fields:
    #             value = getattr(node, field)
    #             visited = self._visit_generic(value)
    #             setattr(node, field, visited)
    #     return self._transform(node)


def set_const(node):
    """Populate type constraints for astroid nodes."""
    # astroid.Const represent a constant node like num/str/bool/None/bytes.
    result = type(node.value)
    node.type_constraints = result
    print(str(node.value) + "\n" + str(result) + "\n")


def set_tuple(node):
    # node_types contains types of elements inside tuple.
    node_types = [node_child.type_constraints for node_child in node.elts]
    node.type_constraints = Tuple[node_types[0], node_types[1]]
    print("(True, 3)")
    print(str(node.type_constraints) + "\n")


def set_list(node):
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
    elif len(node_types) == 0 or len(node_types) > 1:
        node.type_constraints = List

    print("[1, 's']" + "\n" + str(node.type_constraints) + "\n")


def set_dict(node):
    # node_types contains types of elements inside Dict.
    node_types = []
    for key, value in node.items:
        if key.type_constraints not in node_types:
            node_types.append(key.type_constraints)
        if value.type_constraints not in node_types:
            node_types.append(value.type_constraints)

    # parameter of Dict[] must be 2 or 0.
    if len(node_types) == 1:
        node.type_constraints = Dict[node_types[0], node_types[0]]
    elif len(node_types) == 2:
        node.type_constraints = Dict[node_types[0], node_types[1]]
    elif len(node_types) == 0 or len(node_types) > 2:
        node.type_constraints = Dict

    print("dict = {'Name': 'Hayley'}" + "\n" + str(node.type_constraints) + "\n")


def set_binop(node):
    op = node.op
    left_operand = node.left.type_constraints
    right_operand = node.right.type_constraints

    node.type_constraints = left_operand
    if right_operand == int and node.type_constraints ==float:
        node.type_constraints = node.type_constraints
    elif right_operand == float and node.type_constraints == int:
        node.type_constraints = right_operand
    elif right_operand != left_operand:
        warnings.warn('Different types of operands found, binop node %s'
                      'might have a type error.' % node)

    print(str(node.left.value) + " " + str(op) + " " + str(node.right.value) +
          "\n" + str(node.type_constraints) + "\n")


def set_unaryop(node):
    op = node.op
    operand = node.operand.value
    node.type_constraints = type(operand)
    print(str(op) + str(operand) + "\n" + str(node.type_constraints) + "\n")

if __name__ == '__main__':
    # TODO: turn this into a proper test, (UnaryBinOps/List/Tuple/Dict/Const)
    # Creating the TypeVisitor object.
    type_visitor = TypeVisitor()
    # Registering a transform function to astroid nodes.
    type_visitor.register_transform(astroid.Const, set_const)
    type_visitor.register_transform(astroid.List, set_list)
    type_visitor.register_transform(astroid.Tuple, set_tuple)
    type_visitor.register_transform(astroid.Dict, set_dict)
    type_visitor.register_transform(astroid.BinOp, set_binop)
    type_visitor.register_transform(astroid.UnaryOp, set_unaryop)
    with open('examples/type_inference/const.py') as f:
        content = f.read()
    module = astroid.parse(content)
    type_visitor.visit(module)
    # print('Visiting node ' + str(node))
    # print('Type constraints:' + str(node.type_constraints))
