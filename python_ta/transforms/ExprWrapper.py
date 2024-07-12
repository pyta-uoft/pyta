from typing import Dict, List, Union

import astroid
import z3
from astroid import nodes


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

    def __init__(self, expr: nodes.Expr, types=None):
        self.node = expr.value
        if types is None:
            types = {}
        self.types = types

    def reduce(self, node: astroid.NodeNG = None) -> Union[z3.ExprRef, List[z3.ExprRef]]:
        """
        Convert astroid node to z3 expression and return it.
        If an error is encountered or a case is not considered, return None.
        """
        if node is None:
            node = self.node

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
        elif isinstance(node, (nodes.List, nodes.Tuple, nodes.Set)):
            node = self.parse_container_op(node)
        elif isinstance(node, nodes.Subscript):
            node = self.parse_index_op(node)
        else:
            raise Z3ParseException(f"Unhandled node type {type(node)}.")

        return node

    def apply_name(self, name: str) -> z3.ExprRef:
        """
        Set up the appropriate variable representation in Z3 based on name and type.
        If an error is encountered or a case is unconsidered, return None.
        """
        typ = self.types[name]
        type_to_z3 = {
            "int": z3.Int,
            "float": z3.Real,
            "bool": z3.Bool,
            "str": z3.String,
        }
        if typ in type_to_z3:
            x = type_to_z3[typ](name)
        else:
            raise Z3ParseException(f"Unhandled type {typ}.")

        return x

    def parse_compare(self, node: astroid.Compare) -> z3.ExprRef:
        """Convert an astroid Compare node to z3 expression."""
        left, ops = node.left, node.ops
        left = self.reduce(left)
        for item in ops:
            op, right = item
            right = self.reduce(right)
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
        self, left: z3.ExprRef, op: str, right: Union[z3.ExprRef, List[z3.ExprRef]]
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

    def apply_bool_op(self, op: str, values: Union[z3.ExprRef, List[z3.ExprRef]]) -> z3.ExprRef:
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
        left = self.reduce(left)

        return self.apply_unary_op(left, op)

    def parse_bin_op(self, node: astroid.BinOp) -> z3.ExprRef:
        """Convert an astroid BinOp node to a z3 expression."""
        left, op, right = node.left, node.op, node.right
        left = self.reduce(left)
        right = self.reduce(right)

        return self.apply_bin_op(left, op, right)

    def parse_bool_op(self, node: astroid.BoolOp) -> z3.ExprRef:
        """Convert an astroid BoolOp node to a z3 expression."""
        op, values = node.op, node.values
        values = [self.reduce(x) for x in values]

        return self.apply_bool_op(op, values)

    def parse_container_op(
        self, node: Union[nodes.List, nodes.Set, nodes.Tuple]
    ) -> List[z3.ExprRef]:
        """Convert an astroid List, Set, Tuple node to a list of z3 expressions."""
        return [self.reduce(element) for element in node.elts]

    def apply_in_op(
        self, left: z3.ExprRef, right: Union[z3.ExprRef, List[z3.ExprRef], str], negate=False
    ) -> z3.ExprRef:
        """
        Apply `in` or `not in` operator on a list or string and return the
        resulting z3 expression. Raise Z3ParseException if the operands
        do not support `in` operator
        """
        if isinstance(right, list):  # container tyoe (list/set/tuple)
            return (
                z3.And(*[left != element for element in right])
                if negate
                else z3.Or(*[left == element for element in right])
            )
        elif isinstance(right, (str, z3.SeqRef)):  # string literal or variable
            return z3.Not(z3.Contains(right, left)) if negate else z3.Contains(right, left)
        else:
            op = "not in" if negate else "in"
            raise Z3ParseException(
                f"Unhandled binary operation {op} with operator types {left} and {right}."
            )

    def parse_index_op(self, node: nodes.Subscript) -> Union[z3.ExprRef, List[z3.ExprRef]]:
        """Convert an astroid Subscript node to a list of z3 expressions."""
        index = node.slice.value  # TODO: fixed nested expressions inside the index
        value = self.reduce(node.value)
        if isinstance(value, z3.SeqRef):
            # handle negative indexing
            if index < 0:
                index += z3.Length(value)
            return z3.SubString(value, index, index)
