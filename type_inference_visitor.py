from astroid.transforms import TransformVisitor
import astroid


class TypeVisitor(TransformVisitor):
    def _transform(self, node):
        if isinstance(node, astroid.Const):
            print('Visiting node ' + str(node))
            print('Type constraints:' + str(node.type_constraints))


def set_const(node: astroid.Const):
    """Populate type constraints for Const nodes."""
    node.type_constraints = [type(node.value)]


if __name__ == '__main__':
    # TODO: turn this into a proper test
    ending_transformer = TransformVisitor()

    with open('examples/type_inference/const.py') as f:
        content = f.read()

    ending_transformer.register_transform(astroid.Const, set_const)

    module = astroid.parse(content)
    ending_transformer.visit(module)

    ending_visitor = TypeVisitor()
    ending_visitor.visit(module)
