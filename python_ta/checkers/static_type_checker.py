import re
from typing import Optional

from astroid import nodes
from mypy import api
from pylint.checkers import BaseRawFileChecker
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
    options = (
        (
            "mypy-options",
            {
                "default": ["ignore-missing-imports", "follow-imports=skip"],
                "type": "csv",
                "metavar": "<mypy options>",
                "help": "List of configuration flags for mypy",
            },
        ),
    )

    COMMON_PATTERN = (
        r"^(?P<file>[^:]+):(?P<start_line>\d+):(?P<start_col>\d+):"
        r"(?P<end_line>\d+):(?P<end_col>\d+): error: (?P<message>.+) \[(?P<code>[\w-]+)\]"
    )

    SPECIFIC_PATTERNS = {
        "arg-type": re.compile(
            r"Argument (?P<arg_num>\d+) to \"(?P<func_name>[^\"]+)\" has incompatible type \"(?P<incomp_type>[^\"]+)\"; expected \"(?P<exp_type>[^\"]+)\""
        ),
        "assignment": re.compile(
            r"Incompatible types in assignment \(expression has type \"(?P<expr_type>[^\"]+)\", variable has type \"(?P<var_type>[^\"]+)\"\)"
        ),
        "list-item": re.compile(
            r"List item (?P<item_index>\d+) has incompatible type \"(?P<item_type>[^\"]+)\"; expected \"(?P<exp_type>[^\"]+)\""
        ),
        "operator": re.compile(
            r"Unsupported operand types for (?P<operator>\S+) \(\"(?P<left_type>[^\"]+)\" and \"(?P<right_type>[^\"]+)\"\)"
        ),
        "union-attr": re.compile(
            r"Item \"(?P<item_type>[^\"]+)\" of \"[^\"]+\" has no attribute \"(?P<attribute>[^\"]+)\""
        ),
        "dict-item": re.compile(
            r"Dict entry (?P<entry_index>\d+) has incompatible type \"(?P<key_type>[^\"]+)\": \"(?P<value_type>[^\"]+)\"; expected \"(?P<exp_key_type>[^\"]+)\": \"(?P<exp_value_type>[^\"]+)\""
        ),
    }

    def process_module(self, node: nodes.Module) -> None:
        """Run Mypy on the current file and handle type errors."""
        filename = node.file

        mypy_options = ["--show-error-end"]
        for arg in self.linter.config.mypy_options:
            mypy_options.append("--" + arg)

        result, _, _ = api.run([filename] + mypy_options)

        for line in result.splitlines():
            common_match = re.match(self.COMMON_PATTERN, line)
            if not common_match:
                continue

            common_data = common_match.groupdict()

            specific_pattern = self.SPECIFIC_PATTERNS.get(common_data["code"])
            if specific_pattern:
                specific_match = specific_pattern.search(common_data["message"])
                if specific_match:
                    specific_data = specific_match.groupdict()
                    self._add_message(common_data, specific_data)

    def _add_message(self, common_data: dict, specific_data: dict) -> None:
        """Add a message using the common and specific data."""
        code = common_data["code"]
        code_to_msgid = {
            "arg-type": "incompatible-argument-type",
            "assignment": "incompatible-assignment",
            "list-item": "list-item-type-mismatch",
            "operator": "unsupported-operand-types",
            "union-attr": "union-attr-error",
            "dict-item": "dict-item-type-mismatch",
        }
        msgid = code_to_msgid.get(code)
        if not msgid:
            return
        self.add_message(
            msgid,
            line=int(common_data["start_line"]),
            col_offset=int(common_data["start_col"]),
            end_lineno=int(common_data["end_line"]),
            end_col_offset=int(common_data["end_col"]),
            args=tuple(specific_data.values()),
        )


def register(linter: PyLinter) -> None:
    """Register the static type checker with the PyLinter."""
    linter.register_checker(StaticTypeChecker(linter))
