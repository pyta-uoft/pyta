from astroid.transforms import TransformVisitor
import astroid
import warnings


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

    def _transform(self, node):
        """Call matching transforms for the given node if any and return the
        transformed node.
        """
        node_class = node.__class__
        if node_class not in self.transforms:
            # If the node has no transfrom functions, directly return the
            # node type.
            set_const(node)
            return node
        # transforms collects all the transformation functions for node_class.
        transforms = self.transforms[node_class]
        # making a copy of the original node.
        original_node = node
        for transform_func, predicate in transforms:
            if predicate is None or predicate(node):
                transform_node = transform_func(node)
                if transform_node is not None:
                    if node is not original_node:
                        warnings.warn('node %s already got substituted ' %
                                      node)
                    node = transform_node

        print('Visiting node ' + str(node))
        print('Type constraints:' + str(node.type_constraints))
        return node


def set_const(node):
    """Populate type constraints for astroid nodes."""
    if isinstance(node, astroid.Const):
        # # astroid.Const represent a constant node like num/str/bool/None/bytes.
        # if isinstance(node.parent, astroid.UnaryOp):
        #     print(node.value)
        #     Expr(value=astroid.UnaryOp(op=USub(), operand=Name(id='a', ctx=Load())))
        node.type_constraints = [type(node.value)]
    elif isinstance(node, astroid.Tuple):
        node.type_constraints = [type(())]
    elif isinstance(node, astroid.List):
        node.type_constraints = [type([])]
    elif isinstance(node, astroid.Dict):
        node.type_constraints = [type({})]

    elif isinstance(node, astroid.BinOp):
        op = node.op
        left_operand = node.left.value
        right_operand = node.right.value
        result = eval(str(left_operand) + op + str(right_operand))
        node.type_constraints = [type(result)]

    elif isinstance(node, astroid.UnaryOp):
        op = node.op
        operand = node.operand.value
        result = eval(op + str(operand))
        node.type_constraints = [type(result)]


if __name__ == '__main__':
    # TODO: turn this into a proper test, (UnaryBinOps/List/Tuple/Dict/Const)
    # Creating the TypeVisitor object.
    type_visitor = TypeVisitor()
    # Registering a transform function to astroid nodes.
    type_visitor.register_transform(astroid.Const, set_const)
    type_visitor.register_transform(astroid.List, set_const)
    type_visitor.register_transform(astroid.Tuple, set_const)
    type_visitor.register_transform(astroid.Dict, set_const)
    type_visitor.register_transform(astroid.BinOp, set_const)
    type_visitor.register_transform(astroid.UnaryOp, set_const)
    with open('examples/type_inference/const.py') as f:
        content = f.read()
    module = astroid.parse(content)
    type_visitor.visit(module)
