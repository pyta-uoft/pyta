import astroid
from astroid import Uninferable, nodes
from astroid.transforms import TransformVisitor

from ..contracts import parse_assertions
from .ExprWrapper import ExprWrapper


class Z3Visitor:
    def __init__(self):
        """Return a TransformVisitor that sets an environment for every node."""
        visitor = TransformVisitor()
        # Register transforms
        visitor.register_transform(nodes.FunctionDef, self.set_function_def_z3_constraints)
        self.visitor = visitor

    def set_function_def_z3_constraints(self, node: nodes.FunctionDef):
        # Parse types
        types = {}
        annotations = node.args.annotations
        arguments = node.args.args
        for ann, arg in zip(annotations, arguments):
            if ann is None:
                continue
            # TODO: what to do about subscripts ex. Set[int], List[Set[int]], ...
            inferred = ann.inferred()
            if len(inferred) > 0 and inferred[0] is not Uninferable:
                if isinstance(inferred[0], nodes.ClassDef):
                    types[arg.name] = inferred[0].name
        # Parse preconditions
        docstring = node.doc_node.value
        preconditions = parse_assertions(docstring, parse_token="Precondition")
        # Get z3 constraints
        z3_constraints = []
        for pre in preconditions:
            pre = astroid.parse(pre).body[0]
            ew = ExprWrapper(pre, types)
            transformed = ew.reduce()
            if transformed is not None:
                z3_constraints.append(transformed)
        # Set z3 constraints
        node.z3_constraints = z3_constraints
        return node
