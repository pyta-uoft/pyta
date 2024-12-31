import re
from typing import Optional

from astroid import nodes
from mypy import api
from pylint.checkers import BaseRawFileChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class StaticTypeChecker(BaseRawFileChecker):
    """Checker for static type checking using Mypy."""

    name = "static_type_checker"
    msgs = {
        "E9951": (
            "Argument %s to %s has incompatible type %s; expected %s",
            "incompatible-argument-type",
            "Used when a function argument has an incompatible type",
        ),
        "E9952": (
            "Incompatible types in assignment (expression has type %s, variable has type %s)",
            "incompatible-assignment",
            "Used when there is an incompatible assignment",
        ),
        "E9953": (
            "List item %s has incompatible type %s; expected %s",
            "list-item-type-mismatch",
            "Used when a list item has an incompatible type",
        ),
        "E9954": (
            "Unsupported operand types for %s (%s and %s)",
            "unsupported-operand-types",
            "Used when an operation is attempted between incompatible types",
        ),
        "E9955": (
            "Item of type %s in Union has no attribute %s",
            "union-attr-error",
            "Used when accessing an attribute that may not exist on a Union type",
        ),
        "E9956": (
            "Dict entry %s has incompatible type %s: %s; expected %s: %s",
            "dict-item-type-mismatch",
            "Used when a dictionary entry has an incompatible key or value type",
        ),
    }

    @only_required_for_messages(
        "incompatible-argument-type",
        "incompatible-assignment",
        "list-item-type-mismatch",
        "unsupported-operand-types",
        "union-attr-error",
        "dict-item-type-mismatch",
    )
    def process_module(self, node: nodes.NodeNG) -> None:
        """Run Mypy on the current file and print type errors."""
        filename = node.stream().name
        mypy_options = [
            "--ignore-missing-imports",
            "--disable-error-code=call-arg",
            "--show-error-end",
        ]
        result, _, _ = api.run([filename] + mypy_options)
        for line in result.splitlines():
            if line.endswith("[arg-type]"):
                parsed = self._parse_arg_type_information(line.strip())
                if parsed:
                    self.add_message(
                        "incompatible-argument-type",
                        line=parsed["start_line"],
                        col_offset=parsed["start_col"],
                        end_lineno=parsed["end_line"],
                        end_col_offset=parsed["end_col"],
                        args=(
                            parsed["arg_num"],
                            parsed["func_name"],
                            parsed["incomp_type"],
                            parsed["exp_type"],
                        ),
                    )
            elif line.endswith("[assignment]"):
                parsed = self._parse_assignment_information(line.strip())
                if parsed:
                    self.add_message(
                        "incompatible-assignment",
                        line=parsed["start_line"],
                        col_offset=parsed["start_col"],
                        end_lineno=parsed["end_line"],
                        end_col_offset=parsed["end_col"],
                        args=(parsed["expr_type"], parsed["var_type"]),
                    )
            elif line.endswith("[list-item]"):
                parsed = self._parse_list_item_information(line.strip())
                if parsed:
                    self.add_message(
                        "list-item-type-mismatch",
                        line=parsed["start_line"],
                        col_offset=parsed["start_col"],
                        end_lineno=parsed["end_line"],
                        end_col_offset=parsed["end_col"],
                        args=(
                            parsed["item_index"],
                            parsed["item_type"],
                            parsed["exp_type"],
                        ),
                    )
            elif line.endswith("[operator]"):
                parsed = self._parse_operator_information(line.strip())
                if parsed:
                    self.add_message(
                        "unsupported-operand-types",
                        line=parsed["start_line"],
                        col_offset=parsed["start_col"],
                        end_lineno=parsed["end_line"],
                        end_col_offset=parsed["end_col"],
                        args=(
                            parsed["operator"],
                            parsed["left_type"],
                            parsed["right_type"],
                        ),
                    )
            elif line.endswith("[union-attr]"):
                parsed = self._parse_union_attr_information(line.strip())
                if parsed:
                    self.add_message(
                        "union-attr-error",
                        line=parsed["start_line"],
                        col_offset=parsed["start_col"],
                        end_lineno=parsed["end_line"],
                        end_col_offset=parsed["end_col"],
                        args=(parsed["item_type"], parsed["attribute"]),
                    )
            elif line.endswith("[dict-item]"):
                parsed = self._parse_dict_item_information(line.strip())
                if parsed:
                    self.add_message(
                        "dict-item-type-mismatch",
                        line=parsed["start_line"],
                        col_offset=parsed["start_col"],
                        end_lineno=parsed["end_line"],
                        end_col_offset=parsed["end_col"],
                        args=(
                            parsed["entry_index"],
                            parsed["key_type"],
                            parsed["value_type"],
                            parsed["exp_key_type"],
                            parsed["exp_value_type"],
                        ),
                    )

    def _parse_assignment_information(self, message: str):
        pattern = (
            r"^(?P<file>[^:]+):(?P<start_line>\d+):(?P<start_col>\d+):"
            r"(?P<end_line>\d+):(?P<end_col>\d+): error: "
            r"Incompatible types in assignment \(expression has type \"(?P<expr_type>[^\"]+)\", variable has type \"(?P<var_type>[^\"]+)\"\)"
        )
        match = re.search(pattern, message)
        if match:
            return {
                "file": match.group("file"),
                "start_line": int(match.group("start_line")),
                "start_col": int(match.group("start_col")),
                "end_line": int(match.group("end_line")),
                "end_col": int(match.group("end_col")),
                "expr_type": match.group("expr_type"),
                "var_type": match.group("var_type"),
            }
        return None

    def _parse_arg_type_information(self, message: str):
        pattern = (
            r"^(?P<file>[^:]+):(?P<start_line>\d+):(?P<start_col>\d+):"
            r"(?P<end_line>\d+):(?P<end_col>\d+): error: "
            r"Argument (?P<arg_num>\d+) to \"(?P<func_name>[^\"]+)\" has incompatible type \"(?P<incomp_type>[^\"]+)\"; expected \"(?P<exp_type>[^\"]+)\""
        )
        match = re.search(pattern, message)
        if match:
            return {
                "file": match.group("file"),
                "start_line": int(match.group("start_line")),
                "start_col": int(match.group("start_col")),
                "end_line": int(match.group("end_line")),
                "end_col": int(match.group("end_col")),
                "arg_num": int(match.group("arg_num")),
                "func_name": match.group("func_name"),
                "incomp_type": match.group("incomp_type"),
                "exp_type": match.group("exp_type"),
            }
        return None

    def _parse_list_item_information(self, message: str):
        pattern = (
            r"^(?P<file>[^:]+):(?P<start_line>\d+):(?P<start_col>\d+):"
            r"(?P<end_line>\d+):(?P<end_col>\d+): error: "
            r"List item (?P<item_index>\d+) has incompatible type \"(?P<item_type>[^\"]+)\"; expected \"(?P<exp_type>[^\"]+)\""
        )
        match = re.search(pattern, message)
        if match:
            return {
                "file": match.group("file"),
                "start_line": int(match.group("start_line")),
                "start_col": int(match.group("start_col")),
                "end_line": int(match.group("end_line")),
                "end_col": int(match.group("end_col")),
                "item_index": int(match.group("item_index")),
                "item_type": match.group("item_type"),
                "exp_type": match.group("exp_type"),
            }
        return None

    def _parse_operator_information(self, message: str):
        pattern = (
            r"^(?P<file>[^:]+):(?P<start_line>\d+):(?P<start_col>\d+):"
            r"(?P<end_line>\d+):(?P<end_col>\d+): error: "
            r"Unsupported operand types for (?P<operator>\S+) \(\"(?P<left_type>[^\"]+)\" and \"(?P<right_type>[^\"]+)\"\)"
        )
        match = re.search(pattern, message)
        if match:
            return {
                "file": match.group("file"),
                "start_line": int(match.group("start_line")),
                "start_col": int(match.group("start_col")),
                "end_line": int(match.group("end_line")),
                "end_col": int(match.group("end_col")),
                "operator": match.group("operator"),
                "left_type": match.group("left_type"),
                "right_type": match.group("right_type"),
            }
        return None

    def _parse_union_attr_information(self, message: str):
        pattern = (
            r"^(?P<file>[^:]+):(?P<start_line>\d+):(?P<start_col>\d+):"
            r"(?P<end_line>\d+):(?P<end_col>\d+): error: "
            r"Item \"(?P<item_type>[^\"]+)\" of \"[^\"]+\" has no attribute \"(?P<attribute>[^\"]+)\""
        )
        match = re.search(pattern, message)
        if match:
            return {
                "file": match.group("file"),
                "start_line": int(match.group("start_line")),
                "start_col": int(match.group("start_col")),
                "end_line": int(match.group("end_line")),
                "end_col": int(match.group("end_col")),
                "item_type": match.group("item_type"),
                "attribute": match.group("attribute"),
            }
        return None

    def _parse_dict_item_information(self, message: str):
        pattern = (
            r"^(?P<file>[^:]+):(?P<start_line>\d+):(?P<start_col>\d+):"
            r"(?P<end_line>\d+):(?P<end_col>\d+): error: "
            r"Dict entry (?P<entry_index>\d+) has incompatible type \"(?P<key_type>[^\"]+)\": \"(?P<value_type>[^\"]+)\"; expected \"(?P<exp_key_type>[^\"]+)\": \"(?P<exp_value_type>[^\"]+)\""
        )
        match = re.search(pattern, message)
        if match:
            return {
                "file": match.group("file"),
                "start_line": int(match.group("start_line")),
                "start_col": int(match.group("start_col")),
                "end_line": int(match.group("end_line")),
                "end_col": int(match.group("end_col")),
                "entry_index": int(match.group("entry_index")),
                "key_type": match.group("key_type"),
                "value_type": match.group("value_type"),
                "exp_key_type": match.group("exp_key_type"),
                "exp_value_type": match.group("exp_value_type"),
            }
        return None


def register(linter: PyLinter) -> None:
    """Required method to auto-register this checker to the linter"""
    linter.register_checker(StaticTypeChecker(linter))
