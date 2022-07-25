import astroid
from astroid import nodes
from astroid.transforms import TransformVisitor


class Z3Visitor:
    def environment_transformer(self) -> TransformVisitor:
        """Return a TransformVisitor that sets an environment for every node."""
        visitor = TransformVisitor()
        visitor.register_transform(nodes.FunctionDef, self.set_function_def_z3_constraints)
        # TODO: class def
        return visitor

    def set_function_def_z3_constraints(self, node: nodes.FunctionDef):
        pass
