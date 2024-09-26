from __future__ import annotations

from typing import Optional, Union

import astroid
import z3
from astroid import nodes
from pylint.checkers.utils import safe_infer


class Z3ParseException(Exception):
    """
    Raised when a case is not considered when translating an astroid expression node
    into a z3 expression.
    """

    pass


class Z3Parser:
    """
    Class that converts an astroid expression node into a z3 expression.

    Instance attributes:
        - types: dictionary mapping variable names in astroid expression to their type name or z3 variable.
    """

    node: astroid.NodeNG
    types: dict[str, Union[str, z3.ExprRef]]

    def __init__(self, types: Optional[dict[str, Union[str, z3.ExprRef]]] = None):
        if types is None:
            types = {}
        self.types = types

    def parse(self, node: astroid.NodeNG) -> z3.ExprRef:
        """
        Convert astroid node to z3 expression and return it.
        If an error is encountered or a case is not considered, return None.
        """
        if isinstance(node, nodes.BoolOp):
            node = self.parse_bool_op(node)
        elif isinstance(node, nodes.UnaryOp):
            node = self.parse_unary_op(node)
        elif isinstance(node, nodes.Compare):
            node = self.parse_compare(node)
        elif isinstance(node, nodes.BinOp):
            node = self.parse_bin_op(node)
        elif isinstance(node, (nodes.Expr, nodes.Assign)):
            node = self.parse(node.value)
        elif isinstance(node, nodes.Const):
            node = node.value
        elif isinstance(node, nodes.Name):
            node = self.apply_name(node.name)
        elif isinstance(node, nodes.AssignName):
            node = self.apply_name(node.name)
        elif isinstance(node, (nodes.List, nodes.Tuple, nodes.Set)):
            node = self.parse_container_op(node)
        elif isinstance(node, nodes.Subscript):
            node = self.parse_subscript_op(node)
        else:
            raise Z3ParseException(f"Unhandled node type {type(node)}.")

        return node

    def apply_name(self, name: str) -> z3.ExprRef:
        """
        Set up the appropriate variable representation in Z3 based on name and type.
        If an error is encountered or a case is unconsidered, return None.
        """
        typ = self.types.get(name)
        type_to_z3 = {
            "int": z3.Int,
            "float": z3.Real,
            "bool": z3.Bool,
            "str": z3.String,
        }
        if isinstance(typ, z3.ExprRef):  # the value is already a z3 variable
            x = typ
        elif typ in type_to_z3:  # convert string value to z3 variable
            x = type_to_z3[typ](name)
        else:
            raise Z3ParseException(f"Unhandled type {typ}.")

        return x

    def parse_compare(self, node: astroid.Compare) -> z3.ExprRef:
        """Convert an astroid Compare node to z3 expression."""
        left, ops = node.left, node.ops
        left = self.parse(left)
        for item in ops:
            op, right = item
            right = self.parse(right)
            left = self.apply_bin_op(left, op, right)
        return left

    def apply_unary_op(self, left: z3.ExprRef, op: str) -> z3.ExprRef:
        """Apply z3 unary operation indicated by op."""
        op_to_z3 = {
            "not": z3.Not,
        }
        if op in op_to_z3:
            left = op_to_z3[op](left)
        else:
            raise Z3ParseException(f"Unhandled unary operation {op}.")

        return left

    def apply_bin_op(
        self, left: z3.ExprRef, op: str, right: Union[z3.ExprRef, list[z3.ExprRef]]
    ) -> z3.ExprRef:
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
            elif op == "!=":
                return left != right
            elif op == "<=":
                return left <= right
            elif op == ">=":
                return left >= right
            elif op == "<":
                return left < right
            elif op == ">":
                return left > right
            elif op == "in":
                return self.apply_in_op(left, right)
            elif op == "not in":
                return self.apply_in_op(left, right, negate=True)
            else:
                raise Z3ParseException(
                    f"Unhandled binary operation {op} with operator types {left} and {right}."
                )
        except TypeError:
            raise Z3ParseException(f"Operation {op} incompatible with types {left} and {right}.")

    def apply_bool_op(self, op: str, values: Union[z3.ExprRef, list[z3.ExprRef]]) -> z3.ExprRef:
        """Apply boolean operation given by op to values."""
        op_to_z3 = {
            "and": z3.And,
            "or": z3.Or,
            "not": z3.Not,
        }
        if op in op_to_z3:
            value = op_to_z3[op](values)
        else:
            raise Z3ParseException(f"Unhandled boolean operation {op}.")

        return value

    def parse_unary_op(self, node: astroid.UnaryOp) -> z3.ExprRef:
        """Convert an astroid UnaryOp node to a z3 expression."""
        left, op = node.operand, node.op
        left = self.parse(left)
        return self.apply_unary_op(left, op)

    def parse_bin_op(self, node: astroid.BinOp) -> z3.ExprRef:
        """Convert an astroid BinOp node to a z3 expression."""
        left, op, right = node.left, node.op, node.right
        left = self.parse(left)
        right = self.parse(right)

        return self.apply_bin_op(left, op, right)

    def parse_bool_op(self, node: astroid.BoolOp) -> z3.ExprRef:
        """Convert an astroid BoolOp node to a z3 expression."""
        op, values = node.op, node.values
        values = [self.parse(x) for x in values]

        return self.apply_bool_op(op, values)

    def parse_container_op(
        self, node: Union[nodes.List, astroid.Set, astroid.Tuple]
    ) -> list[z3.ExprRef]:
        """Convert an astroid List, Set, Tuple node to a list of z3 expressions."""
        return [self.parse(element) for element in node.elts]

    def apply_in_op(
        self,
        left: Union[z3.ExprRef, str],
        right: Union[z3.ExprRef, list[z3.ExprRef], str],
        negate: bool = False,
    ) -> z3.ExprRef:
        """
        Apply `in` or `not in` operator on a list or string and return the
        resulting z3 expression. Raise Z3ParseException if the operands
        do not support `in` operator
        """
        if isinstance(right, list):  # container type (list/set/tuple)
            return (
                z3.And(*[left != element for element in right])
                if negate
                else z3.Or(*[left == element for element in right])
            )
        elif isinstance(left, (str, z3.SeqRef)) and isinstance(
            right, (str, z3.SeqRef)
        ):  # string literal or variable
            return z3.Not(z3.Contains(right, left)) if negate else z3.Contains(right, left)
        else:
            op = "not in" if negate else "in"
            raise Z3ParseException(
                f"Unhandled binary operation {op} with operator types {left} and {right}."
            )

    def _parse_number_literal(self, node: astroid.NodeNG) -> Optional[Union[int, float]]:
        """
        If the subtree from `node` represent a number literal, return the value
        Otherwise, return None
        """
        # positive number
        if isinstance(node, nodes.Const) and isinstance(node.value, (int, float)):
            return node.value
        # negative number
        elif (
            isinstance(node, nodes.UnaryOp)
            and node.op == "-"
            and isinstance(node.operand, nodes.Const)
            and isinstance(node.operand.value, (int, float))
        ):
            return -node.operand.value
        else:
            return None

    def parse_subscript_op(self, node: astroid.Subscript) -> z3.ExprRef:
        """
        Convert an astroid Subscript node to z3 expression.
        This method only supports string values and integer literal (both positive and negative) indexes
        """
        value = self.parse(node.value)
        slice = node.slice

        # check for invalid node type
        if not z3.is_seq(value):
            raise Z3ParseException(f"Unhandled subscript operand type {value}")

        # handle indexing
        index = self._parse_number_literal(slice)
        if isinstance(index, int):
            return z3.SubString(value, index, 1)

        # handle slicing
        if isinstance(slice, nodes.Slice):
            lower = 0 if slice.lower is None else self._parse_number_literal(slice.lower)
            upper = (
                z3.Length(value) if slice.upper is None else self._parse_number_literal(slice.upper)
            )
            step = 1 if slice.step is None else self._parse_number_literal(slice.step)

            if not (
                isinstance(lower, int)
                and isinstance(upper, (int, z3.ArithRef))
                and isinstance(step, int)
            ):
                raise Z3ParseException(f"Invalid slicing indexes {lower}, {upper}, {step}")

            if step == 1:
                return z3.SubString(value, lower, upper - lower)

            # unhandled case: the upper bound is indeterminant
            if step != 1 and upper == z3.Length(value):
                raise Z3ParseException(
                    "Unable to convert a slicing operation with a non-unit step length and an indeterminant upper bound"
                )

            return z3.Concat(*(z3.SubString(value, i, 1) for i in range(lower, upper, step)))

        raise Z3ParseException(f"Unhandled subscript operator type {slice}")

    def parse_arguments(self, node: astroid.Arguments) -> dict[str, z3.ExprRef]:
        """Convert an astroid Arguments node's parameters to z3 variables."""
        z3_vars = {}

        annotations = node.annotations
        arguments = node.args
        for ann, arg in zip(annotations, arguments):
            if ann is None:
                continue

            inferred = safe_infer(ann)
            if inferred is None or not isinstance(inferred, astroid.ClassDef):
                continue

            self.types[arg.name] = inferred.name

            if arg.name in self.types and self.types[arg.name] in {"int", "float", "bool", "str"}:
                z3_vars[arg.name] = self.parse(arg)

        return z3_vars
