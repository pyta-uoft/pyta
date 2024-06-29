from typing import Any, Dict, List, Optional, Union

import astroid
from astroid import nodes

try:
    from z3 import And, Bool, ExprRef, Int, Not, Or, Real
except ImportError:
    ExprRef, Int, Real, Bool, And, Or, Not = Any, Any, Any, Any, Any, Any, Any


class Z3ParseException(Exception):
    """
    Raised when a case is not considered when translating an astroid expression node
    into a z3 expression.
    """

    pass


class ExprWrapper:
    """
    Wrapper class to convert an astroid expression node into a z3 expression.

    Instance attributes:
        - node: astroid node obtained given by the value attribute of astroid expression.
        - types: dictionary mapping variable names in astroid expression to their type name.
    """

    node: astroid.NodeNG
    types: Dict[str, str]

    def __init__(self, node: astroid.NodeNG, types={}):
        self.types = types

        if isinstance(node, astroid.Expr):
            self.node = node.value  # take node attribute to be the value of the expression
        elif isinstance(node, astroid.Arguments):
            self.node = node  # take node attribute to be the function declaration node itself
        else:
            raise Z3ParseException(
                "Node must be an astroid expression or function declaration's arguments node."
            )

    def reduce(self, node: astroid.NodeNG = None) -> ExprRef:
        """
        Convert astroid node to z3 expression and return it.
        If an error is encountered or a case is not considered, return None.
        """
        if node is None:
            node = self.node

        if ExprRef is Any:
            return node

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
            node = self.apply_name(node.name)
        elif isinstance(node, nodes.Assign):
            node = self.reduce(node.targets[0])
        elif isinstance(node, nodes.AssignName):
            node = self.apply_name(node.name)
        # elif isinstance(node, nodes.Arguments):
        #     node = self.parse_arguments(node)[0]
        # elif isinstance(node, nodes.FunctionDef):
        #     node = self.parse_arguments(node.args)[0]
        else:
            raise Z3ParseException(f"Unhandled node type {type(node)}.")

        return node

    def apply_name(self, name: str) -> ExprRef:
        """
        Set up the appropriate variable representation in Z3 based on name and type.
        If an error is encountered or a case is unconsidered, return None.
        """
        typ = self.types[name]
        type_to_z3 = {
            "int": Int,
            "float": Real,
            "bool": Bool,
        }
        if typ in type_to_z3:
            x = type_to_z3[typ](name)
        else:
            raise Z3ParseException(f"Unhandled type {typ}.")

        return x

    def parse_compare(self, node: astroid.Compare) -> ExprRef:
        """Convert an astroid Compare node to z3 expression."""
        left, ops = node.left, node.ops
        left = self.reduce(left)
        for item in ops:
            op, right = item
            right = self.reduce(right)
            left = self.apply_bin_op(left, op, right)
        return left

    def apply_unary_op(self, left: ExprRef, op: str) -> ExprRef:
        """Apply z3 unary operation indicated by op."""
        op_to_z3 = {
            "not": Not,
        }
        if op in op_to_z3:
            left = op_to_z3[op](left)
        else:
            raise Z3ParseException(f"Unhandled unary operation {op}.")

        return left

    def apply_bin_op(self, left: ExprRef, op: str, right: ExprRef) -> ExprRef:
        """Given left, right, op, apply the binary operation."""
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
                raise Z3ParseException(f"Unhandled binary operation {op}.")
        except TypeError:
            raise Z3ParseException(f"Operation {op} incompatible with types {left} and {right}.")

    def apply_bool_op(self, op: str, values: Union[ExprRef, List[ExprRef]]) -> ExprRef:
        """Apply boolean operation given by op to values."""
        op_to_z3 = {
            "and": And,
            "or": Or,
            "not": Not,
        }
        if op in op_to_z3:
            value = op_to_z3[op](values)
        else:
            raise Z3ParseException(f"Unhandled boolean operation {op}.")

        return value

    def parse_unary_op(self, node: astroid.UnaryOp) -> ExprRef:
        """Convert an astroid UnaryOp node to a z3 expression."""
        left, op = node.operand, node.op
        left = self.reduce(left)
        return self.apply_unary_op(left, op)

    def parse_bin_op(self, node: astroid.BinOp) -> ExprRef:
        """Convert an astroid BinOp node to a z3 expression."""
        left, op, right = node.left, node.op, node.right
        left = self.reduce(left)
        right = self.reduce(right)

        return self.apply_bin_op(left, op, right)

    def parse_bool_op(self, node: astroid.BoolOp) -> ExprRef:
        """Convert an astroid BoolOp node to a z3 expression."""
        op, values = node.op, node.values
        values = [self.reduce(x) for x in values]
        return self.apply_bool_op(op, values)

    def parse_arguments(self, node: astroid.Arguments) -> Dict[str, ExprRef]:
        """Convert an astroid Arguments node's parameters to z3 variables."""
        z3_vars = {}  # initialize mapping of z3 variables

        annotations = node.annotations
        arguments = node.args
        for ann, arg in zip(annotations, arguments):
            if ann is None:
                continue
            inferred = ann.inferred()
            if (
                len(inferred) > 0
                and inferred[0] is not astroid.Uninferable
                and isinstance(inferred[0], astroid.ClassDef)
            ):
                self.types[arg.name] = inferred[0].name

            if arg.name in self.types and self.types[arg.name] in ["int", "float", "bool"]:
                z3_vars[arg.name] = self.reduce(arg)

        return z3_vars
