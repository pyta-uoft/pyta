from __future__ import annotations

import astroid
from astroid import AstroidError, nodes
from astroid.transforms import TransformVisitor
from astroid.util import safe_infer
from z3.z3types import Z3Exception

from ..contracts import parse_assertions
from ..z3.z3_parser import Z3ParseException, Z3Parser


class Z3Visitor:
    """
    The class responsible for visiting astroid nodes (currently only FunctionDef nodes),
    parsing preconditions, and converting them to z3 expressions to be appended in the
    z3_constraints attribute of the node.
    """

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
            # TODO: what to do about subscripts ex. set[int], list[set[int]], ...
            inferred = safe_infer(ann)
            if isinstance(inferred, nodes.ClassDef):
                types[arg.name] = inferred.name
        # Parse preconditions
        preconditions = parse_assertions(node, parse_token="Precondition")
        # Get z3 constraints
        z3_constraints = []
        for pre in preconditions:
            pre = astroid.parse(pre).body[0]
            parser = Z3Parser(types)
            try:
                transformed = parser.parse(pre)
            except (AstroidError, Z3Exception, Z3ParseException):
                transformed = None
            if transformed is not None:
                z3_constraints.append(transformed)
        # Set z3 constraints
        node.z3_constraints = z3_constraints
        return node
