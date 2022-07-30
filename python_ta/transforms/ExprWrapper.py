from typing import Optional

import astroid
import z3
from astroid import nodes


class ExprWrapper:
    node: astroid.NodeNG
    types = {}
    variable_counter = 0

    def __init__(self, expr: nodes.Expr, types={}):
        self.node = expr.value
        self.types = types
        self.transformed = self.reduce(self.node)

    def reduce(self, node: astroid.NodeNG) -> Optional[astroid.NodeNG]:
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
            # Throw some error
            pass

        return node

    def apply_name(self, name: str, typ: str):
        """Set up the appropriate variable representation in Z3 based on name and type (typ)."""
        # TODO: determine full list of supported types
        if typ == "int":
            return z3.Int(name)
        if typ == "float":
            return z3.Real(name)
        if typ == "bool":
            return z3.Bool(name)

    def parse_compare(self, node: astroid.Compare):
        left, ops = node.left, node.ops
        left = self.reduce(left)
        for item in ops:
            op, right = item
            right = self.reduce(right)
            left = self.apply_bin_op(left, op, right)
        return left

    def apply_unary_op(self, left, op):
        if op == "not":
            return z3.Not(left)

    def apply_bin_op(self, left, op, right):
        """Given left, right, op, apply the binary operation."""
        # Todo: find out which binary operations are supported
        if op == "+":
            return left + right
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

    def apply_bool_op(self, op, values):
        if op == "and":
            return z3.And(values)
        elif op == "or":
            return z3.Or(values)

    def parse_unary_op(self, node: astroid.UnaryOp):
        left, op = node.operand, node.op
        left = self.reduce(left)
        return self.apply_unary_op(left, op)

    def parse_bin_op(self, node: astroid.BinOp):
        """Recurse on node.left, node.op, node.right."""
        # TODO: determine full list of what node.left or node.right can be
        left, op, right = node.left, node.op, node.right
        left = self.reduce(left)
        right = self.reduce(right)
        return self.apply_bin_op(left, op, right)

    def parse_bool_op(self, node: astroid.BoolOp):
        op, values = node.op, node.values
        values = [self.reduce(x) for x in values]
        return self.apply_bool_op(op, values)
