from typing import Optional

import astroid
import z3
from astroid import nodes


class ExprWrapper:
    node: astroid.NodeNG
    types = {}
    variable_counter = 0

    def __init__(self, expr: nodes.Expr):
        self.node = expr.value

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
        elif isinstance(node, nodes.Call):
            node = self.parse_call(node)
        elif isinstance(node, nodes.GeneratorExp):
            node = self.parse_generator_exp(node)
        else:
            # Throw some error
            pass

        return node

    def apply_name(self, name: str, typ: str):
        """Set up the appropriate variable representation in Z3 based on name and type (typ)."""
        # TODO: determine full list of supported types
        if typ == "int":
            return z3.Int(name)
        if typ == "bool":
            return z3.Bool(name)

    def parse_compare(self, node: astroid.NodeNG):
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

    def parse_unary_op(self, node: astroid.NodeNG):
        left, op = node.operand, node.op
        left = self.reduce(left)
        return self.apply_unary_op(left, op)

    def parse_bin_op(self, node: astroid.NodeNG):
        """Recurse on node.left, node.op, node.right."""
        # TODO: determine full list of what node.left or node.right can be
        left, op, right = node.left, node.op, node.right
        left = self.reduce(left)
        right = self.reduce(right)
        return self.apply_bin_op(left, op, right)

    def parse_bool_op(self, node: astroid.NodeNG):
        op, values = node.op, node.values
        values = [self.reduce(x) for x in values]
        return self.apply_bool_op(op, values)

    def parse_generator_exp(self, node: astroid.GeneratorExp):
        element = node.elt
        generators = node.generators
        conditions = []
        for gen in generators:
            self.types[gen.target.name] = self.types[gen.iter.name]
            conditions.extend(gen.ifs)
        element = self.reduce(element)
        conditions = [self.reduce(condition) for condition in conditions]
        left = True
        for condition in conditions:
            left = z3.And(left, condition)
        return z3.Implies(left, element)

    def parse_all(self, node: nodes.Call):
        args = node.args
        args = [self.reduce(arg) for arg in args]
        if len(args) == 0:
            # TODO: what to do here
            return None
        left = True
        for arg in args:
            left = z3.And(left, arg)
        return left

    def parse_call(self, node: nodes.Call):
        func = node.func
        func_name = func.name
        if func_name == "all":
            return self.parse_all(node)


# Testing
# code = "all(x >= 0 for x in s if x < 0)"
# expr = astroid.parse(code).body[0]
# wrapper = ExprWrapper(expr)
# wrapper.types = {"s": "int"}
# print(wrapper.reduce(wrapper.node))
