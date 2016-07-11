from astroid.transforms import TransformVisitor
import astroid
import warnings
import typing
from typing import Tuple, Mapping, Sequence, TypeVar, List


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
    node.type_constraints = tuple(node_child.type_constraints for node_child
                                  in node.elts)
    print("(True, 3)")
    print(str(node.type_constraints) + "\n")


def set_list(node):
    node.type_constraints = list(node_child.type_constraints for node_child in
                             node.elts)
    print("[1, 2342]" + "\n" + str(node.type_constraints) + "\n")


def set_dict(node):
    # result = dict
    # node.type_constraints = result
    result = {}
    for key, value in node.items:
        result[key.type_constraints] = value.type_constraints
    node.type_constraints = result
    print("dict = {'Name': 'Hayley'}" + "\n" + str(node.type_constraints) + "\n")


def set_binop(node):
    op = node.op
    left_operand = node.left.type_constraints
    right_operand = node.right.type_constraints

    result = [left_operand]
    if right_operand==int and left_operand==float:
        node.type_constraints = left_operand
    elif right_operand==float and left_operand==int:
        node.type_constraints = right_operand
    elif right_operand not in result:
        warnings.warn('Different types of operands found, binop node %s'
                      'might have a type error.' % node)
    else:
        node.type_constraints = left_operand

    print(str(node.left.value) + " " + str(op) + " " + str(node.right.value) +
          "\n" + str(result) + "\n")


def set_unaryop(node):
    if isinstance(node, astroid.UnaryOp):
        op = node.op
        operand = node.operand.value
        node.type_constraints = type(operand)
        print(str(op) + str(operand) + "\n" + str(node.type_constraints) + "\n")
    else:
        warnings.warn('node %s is not unary operator type.' % node)


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
