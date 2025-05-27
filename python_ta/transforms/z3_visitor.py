from __future__ import annotations

import astroid
import z3
from astroid import AstroidError, nodes
from astroid.transforms import TransformVisitor
from astroid.util import safe_infer
from z3.z3types import Z3Exception

from ..contracts import parse_assertions
from ..z3.z3_parser import Z3ParseException, Z3Parser


class Z3Visitor:
    """
    Visits FunctionDef nodes, parses their Preconditions docstrings,
    and attaches the resulting Z3 expressions to node.z3_constraints.
    """

    def __init__(self):
        visitor = TransformVisitor()
        visitor.register_transform(nodes.FunctionDef, self.set_function_def_z3_constraints)
        self.visitor = visitor

    def set_function_def_z3_constraints(self, node: nodes.FunctionDef):
        # 1) Build a map of argument names to their inferred types.
        types: dict[str, str] = {}
        for ann, arg in zip(node.args.annotations, node.args.args):
            if ann is None:
                continue
            inferred = safe_infer(ann)
            if isinstance(inferred, nodes.ClassDef):
                types[arg.name] = inferred.name

        # 2) Extract the list of precondition strings.
        preconditions = parse_assertions(node, parse_token="Precondition")

        # 3) Parse each one into a Z3 expression.
        z3_constraints: list[z3.ExprRef] = []
        for pre in preconditions:
            try:
                # Parse via astroid to get an Expr node,
                # then hand it off to Z3Parser.
                ast_node = astroid.parse(pre).body[0]
                parser = Z3Parser(types)
                transformed = parser.parse(ast_node)
            except (AstroidError, Z3Exception, Z3ParseException):
                transformed = None

            if transformed is not None:
                z3_constraints.append(transformed)

        # Attach to the FunctionDef node
        node.z3_constraints = z3_constraints
        return node
