from astroid.transforms import TransformVisitor
import astroid
import warnings
import typing


class TypeVisitor(TransformVisitor):

    def _visit(self, node):
        # If node is an instance of List/Tuple/Dict, instead of breaking
        # down to smaller pieces of node such as const nodes, keep the
        # bigger piece and directly use an transform function on it.
        if isinstance(node, astroid.List) or isinstance(node, astroid.Tuple)\
                or isinstance(node, astroid.Dict):
            return self._transform(node)
        if hasattr(node, '_astroid_fields'):
            for field in node._astroid_fields:
                value = getattr(node, field)
                visited = self._visit_generic(value)
                setattr(node, field, visited)
        return self._transform(node)


def set_const(node):
    """Populate type constraints for astroid nodes."""
    if isinstance(node, astroid.Const):
        # astroid.Const represent a constant node like num/str/bool/None/bytes.
        result = [type(node.value)]
        node.type_constraints = result
        print(str(node.value) + "\n" + str(result) + "\n")
    else:
        warnings.warn('node %s is not const type.' % node)


def set_tuple(node):
    if isinstance(node, astroid.Tuple):
        result = [tuple]
        node.type_constraints = result
        print("(" + ")" + "\n" + str(result) + "\n")
    else:
        warnings.warn('node %s is not tuple type.' % node)


def set_list(node):
    if isinstance(node, astroid.List):
        result = [list]
        node.type_constraints = result
        print("[" + "]" + "\n" + str(result) + "\n")
    else:
        warnings.warn('node %s is not list type.' % node)


def set_dict(node):
    if isinstance(node, astroid.Dict):
        result = [dict]
        node.type_constraints = result
        print("{" + "}" + "\n" + str(result) + "\n")
    else:
        warnings.warn('node %s is not dict type.' % node)


def set_binop(node):
    if isinstance(node, astroid.BinOp):
        op = node.op
        left_operand = node.left.value
        right_operand = node.right.value

        # Using typing.Union to find both types of the operands, if they are
        # found as different types, such as list and string, return an type
        # error.
        result = [typing.Union[type(left_operand), type(right_operand)]]

        # if int and float were added togeter, take float as the type
        # constraint.
        if result == [typing.Union[int, float]] or result == [typing.Union[
                      float, int]]:
            result = [typing.Union[float, float]]
        if len(result) > 1:
            warnings.warn('Different types of operands found, binop node %s'
                          'might have a type error.' % node)
        print(str(left_operand) + " " + str(op) + " " + str(right_operand) +
              "\n" + str(result) + "\n")

        # result = eval(str(left_operand) + op + str(right_operand))
        # node.type_constraints = [type(result)]
        node.type_constraints = result
    else:
        warnings.warn('node %s is not binary operator type.' % node)


def set_unaryop(node):
    if isinstance(node, astroid.UnaryOp):
        op = node.op
        operand = node.operand.value

        # result = eval(op + str(operand))
        # node.type_constraints = [type(result)]
        result = [type(operand)]
        node.type_constraints = result
        print(str(op) + str(operand) + "\n" + str(result) + "\n")
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
