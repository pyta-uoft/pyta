from typing import Dict, Optional

import astroid
import z3
from astroid import nodes


class ExprWrapper:
    """
    Wrapper class to convert an astroid expression node into a z3 expression.

    Instance attributes:
        - node: astroid node obtained given by the value attribute of astroid expression.
        - types: dictionary mapping variable names in astroid expression to their type name.
    """

    node: astroid.NodeNG
    types: Dict[str, str]

    def __init__(self, expr: nodes.Expr, types=None):
        self.node = expr.value
        if self.types is None:
            self.types = {}

    def reduce(self, node: astroid.NodeNG = None) -> Optional[z3.ExprRef]:
        """
        Convert astroid node to z3 expression and return it.
        If an error is encountered or a case is not considered, return None.
        """
        if node is None:
            node = self.node

        try:
            if isinstance(node, nodes.BoolOp):
                node = self.parse_bool_op(node)
            elif isinstance(node, nodes.UnaryOp):
                node = self.parse_unary_op(node)
            elif isinstance(node, nodes.Compare):
                node = self.parse_compare(node)
            elif isinstance(node, nodes.BinOp):
                node = self.parse_bin_op(node)
            elif isinstance(node, nodes.Const):
                node = node.value
            elif isinstance(node, nodes.Name):
                node = self.apply_name(node.name, self.types[node.name])
            else:
                node = None

            return node
        except Exception:
            return None

    def apply_name(self, name: str, typ: str) -> Optional[z3.ExprRef]:
        """Set up the appropriate variable representation in Z3 based on name and type.
        If an error is encountered or a case is unconsidered, return None."""
        # TODO: determine full list of supported types
        if typ == "int":
            return z3.Int(name)
        if typ == "float":
            return z3.Real(name)
        if typ == "bool":
            return z3.Bool(name)

        return None

    def parse_compare(self, node: astroid.Compare) -> Optional[z3.ExprRef]:
        left, ops = node.left, node.ops
        # ERROR: left, right can be None at any point in the execution
        left = self.reduce(left)
        for item in ops:
            op, right = item
            right = self.reduce(right)
            left = self.apply_bin_op(left, op, right)
        return left

    def apply_unary_op(self, left, op) -> Optional[z3.ExprRef]:
        # ERROR: left can be None
        # ERROR: see apply_bool_op ERROR comments
        if left is None:
            return None
        try:
            if op == "not":
                return z3.Not(left)
            else:
                return None
        except z3.z3types.Z3Exception:
            return None

    def apply_bin_op(self, left, op, right) -> Optional[z3.ExprRef]:
        """Given left, right, op, apply the binary operation."""
        # ERROR: left or right can be None
        if left is None or right is None:
            return None
        # TODO: find out which binary operations are supported
        # ERROR: unsupported operation ie. bool + bool (raises TypeError)
        try:
            if op == "+":
                return left + right
            elif op == "-":
                return left - right
            elif op == "*":
                return left * right
            elif op == "/":
                return left / right
            elif op == "**":
                return left**right
            elif op == "==":
                return left == right
            elif op == "<=":
                return left <= right
            elif op == ">=":
                return left >= right
            elif op == "<":
                return left < right
            elif op == ">":
                return left > right
            else:
                return None
        except TypeError:
            return None

    def apply_bool_op(self, op, values) -> Optional[z3.ExprRef]:
        # ERROR: z3.Not does not take array values (raises Z3Exception)
        # ERROR: something like z3.And(1) (raises Z3Exception)
        try:
            if op == "and":
                return z3.And(values)
            elif op == "or":
                return z3.Or(values)
            elif op == "not":
                return z3.Not(values)
            else:
                return None
        except z3.z3types.Z3Exception:
            return None

    def parse_unary_op(self, node: astroid.UnaryOp) -> Optional[z3.ExprRef]:
        left, op = node.operand, node.op
        left = self.reduce(left)
        return self.apply_unary_op(left, op)

    def parse_bin_op(self, node: astroid.BinOp) -> Optional[z3.ExprRef]:
        """Recurse on node.left, node.op, node.right."""
        left, op, right = node.left, node.op, node.right
        left = self.reduce(left)
        right = self.reduce(right)
        return self.apply_bin_op(left, op, right)

    def parse_bool_op(self, node: astroid.BoolOp):
        op, values = node.op, node.values
        values = [self.reduce(x) for x in values]
        return self.apply_bool_op(op, values)
