from __future__ import annotations

from typing import Optional, Union

import astroid
import z3
from astroid import nodes
from pylint.checkers.utils import safe_infer


class Z3ParseException(Exception):
    """Raised when an AST node case is not handled by this parser."""
    pass


class Z3Parser:
    """
    Converts an astroid expression node into a Z3 expression.
    `types` maps argument names to their annotated type (e.g. "int", "str").
    """

    def __init__(self,
                 types: Optional[dict[str, Union[str, z3.ExprRef]]] = None):
        self.types = types or {}

    def parse(self, node: astroid.NodeNG) -> Union[z3.ExprRef, list[z3.ExprRef]]:
        # ── Special-case empty set() calls ──
        if isinstance(node, nodes.Call) \
           and isinstance(node.func, nodes.Name) \
           and node.func.name == "set" \
           and not node.args:
            return []

        # ── Standard dispatch ──
        if isinstance(node, nodes.BoolOp):
            return self.parse_bool_op(node)
        if isinstance(node, nodes.UnaryOp):
            return self.parse_unary_op(node)
        if isinstance(node, nodes.Compare):
            return self.parse_compare(node)
        if isinstance(node, nodes.BinOp):
            return self.parse_bin_op(node)
        if isinstance(node, (nodes.Expr, nodes.Assign)):
            return self.parse(node.value)
        if isinstance(node, nodes.Const):
            return node.value
        if isinstance(node, (nodes.Name, nodes.AssignName)):
            return self.apply_name(node.name)
        if isinstance(node, (nodes.List, nodes.Tuple, nodes.Set)):
            return self.parse_container_op(node)
        if isinstance(node, nodes.Subscript):
            return self.parse_subscript_op(node)

        raise Z3ParseException(f"Unhandled node type {type(node)}.")

    def apply_name(self, name: str) -> z3.ExprRef:
        type_map = {
            "int": z3.Int,
            "float": z3.Real,
            "bool": z3.Bool,
            "str": z3.String,
        }
        typ = self.types.get(name)
        if isinstance(typ, z3.ExprRef):
            return typ
        if typ in type_map:
            return type_map[typ](name)
        raise Z3ParseException(f"Unhandled type {typ} for variable {name}.")

    def parse_compare(self, node: astroid.Compare) -> z3.ExprRef:
        left = self.parse(node.left)
        for op, right_node in node.ops:
            right = self.parse(right_node)
            left = self.apply_bin_op(left, op, right)
        return left

    def parse_bool_op(self, node: astroid.BoolOp) -> z3.ExprRef:
        vals = [self.parse(v) for v in node.values]
        if node.op == "and":
            return z3.And(*vals)
        if node.op == "or":
            return z3.Or(*vals)
        raise Z3ParseException(f"Unhandled boolean op {node.op}.")

    def parse_unary_op(self, node: astroid.UnaryOp) -> z3.ExprRef:
        val = self.parse(node.operand)
        if node.op == "not":
            return z3.Not(val)
        raise Z3ParseException(f"Unhandled unary op {node.op}.")

    def parse_bin_op(self, node: astroid.BinOp) -> z3.ExprRef:
        l = self.parse(node.left)
        r = self.parse(node.right)
        return self.apply_bin_op(l, node.op, r)

    def parse_container_op(self,
                           node: Union[nodes.List, astroid.Set,
                                       astroid.Tuple]) -> list[z3.ExprRef]:
        return [self.parse(el) for el in node.elts]

    def apply_bin_op(self, left: z3.ExprRef, op: str,
                     right: Union[z3.ExprRef, list[z3.ExprRef]]) -> z3.ExprRef:
        try:
            if op == "+":
                return left + right
            if op == "-":
                return left - right
            if op == "*":
                return left * right
            if op == "/":
                return left / right
            if op == "**":
                return left**right
            if op == "==":
                return left == right
            if op == "!=":
                return left != right
            if op == "<=":
                return left <= right
            if op == ">=":
                return left >= right
            if op == "<":
                return left < right
            if op == ">":
                return left > right
            if op == "in":
                return self.apply_in_op(left, right)
            if op == "not in":
                return self.apply_in_op(left, right, negate=True)
        except TypeError:
            raise Z3ParseException(f"Incompatible op {op} for {left}, {right}.")
        raise Z3ParseException(f"Unhandled binary op {op}.")

    def apply_in_op(self,
                    left: Union[z3.ExprRef, str],
                    right: Union[list[z3.ExprRef], str],
                    negate: bool = False) -> z3.ExprRef:
        # Empty container → False for `in`, True for `not in`
        if isinstance(right, list):
            if not right:
                return z3.BoolVal(False) if not negate else z3.BoolVal(True)
            if negate:
                return z3.And(*[left != elt for elt in right])
            return z3.Or(*[left == elt for elt in right])

        # String containment
        if isinstance(left, (str, z3.SeqRef)) and isinstance(
                right, (str, z3.SeqRef)):
            return z3.Not(z3.Contains(right,
                                      left)) if negate else z3.Contains(
                                          right, left)

        op = "not in" if negate else "in"
        raise Z3ParseException(f"Unhandled op {op} for types {left}, {right}.")

    def _parse_number_literal(self, node: astroid.NodeNG
                              ) -> Optional[Union[int, float]]:
        if isinstance(node, nodes.Const) and isinstance(node.value,
                                                        (int, float)):
            return node.value
        if (isinstance(node, nodes.UnaryOp) and node.op == "-"
                and isinstance(node.operand, nodes.Const)
                and isinstance(node.operand.value, (int, float))):
            return -node.operand.value
        return None

    def parse_subscript_op(self, node: astroid.Subscript) -> z3.ExprRef:
        seq = self.parse(node.value)
        if not z3.is_seq(seq):
            raise Z3ParseException(f"Unhandled subscript type {seq}")

        idx = self._parse_number_literal(node.slice)
        if isinstance(idx, int):
            return z3.SubString(seq, idx, 1)

        if isinstance(node.slice, nodes.Slice):
            low = 0 if node.slice.lower is None else self._parse_number_literal(
                node.slice.lower)
            up = (z3.Length(seq)
                  if node.slice.upper is None else self._parse_number_literal(
                      node.slice.upper))
            st = 1 if node.slice.step is None else self._parse_number_literal(
                node.slice.step)

            if not (isinstance(low, int) and isinstance(up, (int,
                                                             z3.ArithRef))
                    and isinstance(st, int)):
                raise Z3ParseException(
                    f"Invalid slice indexes {low},{up},{st}")

            if st == 1:
                return z3.SubString(seq, low, up - low)

            if st != 1 and up == z3.Length(seq):
                raise Z3ParseException(
                    "Cannot convert slice with non-unit step and unknown upper")

            return z3.Concat(
                *(z3.SubString(seq, i, 1) for i in range(low, up, st)))

        raise Z3ParseException(f"Unhandled slice type {node.slice}")

    def parse_arguments(self, node: astroid.Arguments) -> dict[str, z3.ExprRef]:
        z3_vars: dict[str, z3.ExprRef] = {}
        for ann, arg in zip(node.annotations, node.args):
            if ann is None:
                continue
            inferred = safe_infer(ann)
            if not isinstance(inferred, astroid.ClassDef):
                continue
            self.types[arg.name] = inferred.name
            if arg.name in self.types and self.types[arg.name] in {
                    "int", "float", "bool", "str"
            }:
                z3_vars[arg.name] = self.parse(arg)
        return z3_vars
