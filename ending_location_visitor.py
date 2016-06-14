from astroid.transforms import TransformVisitor
import astroid


class EndingVisitor(TransformVisitor):
    def _transform(self, node):
        if isinstance(node, astroid.Const):
            print('Visiting node ' + str(node))
            print('Lines {} to {}'.format(node.lineno, node.end_lineno))
            print('Cols {} to {}'.format(node.col_offset, node.end_col_offset))


def set_const(node: astroid.Const):
    """Populate ending locations for Const nodes."""
    node.end_lineno = node.lineno
    node.end_col_offset = node.col_offset + len(str(node.value))


if __name__ == '__main__':
    # TODO: turn this into a proper test
    ending_transformer = TransformVisitor()

    with open('examples/ending_locations/const.py') as f:
        content = f.read()

    ending_transformer.register_transform(astroid.Const, set_const)

    module = astroid.parse(content)
    ending_transformer.visit(module)

    ending_visitor = EndingVisitor()
    ending_visitor.visit(module)
