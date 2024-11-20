import re
from typing import Optional

import astroid
from astroid import nodes
from mypy import api
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class StaticTypeChecker(BaseChecker):
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
            "mypy-ignore-errors",
            {
                "default": (),
                "type": "csv",
                "metavar": "<mypy-ignore-errors>",
                "help": "List of Mypy error codes to ignore",
            },
        ),
    )

    def __init__(self, linter: Optional["PyLinter"] = None) -> None:
        """Initialize the StaticTypeChecker."""
        super().__init__(linter=linter)
        self._module_stack = []

    @only_required_for_messages(
        "incompatible-argument-type",
        "incompatible-assignment",
        "list-item-type-mismatch",
        "unsupported-operand-types",
        "union-attr-error",
        "dict-item-type-mismatch",
    )
    def visit_module(self, node: nodes.Module) -> None:
        """Run Mypy on the current module and collect type errors."""
        print("Visiting module")
        filename = node.file
        print(f"Filename: {filename}")
        mypy_options = [
            "--ignore-missing-imports",
            "--disable-error-code=call-arg",
        ] + list(self.linter.config.mypy_ignore_errors)
        result, _, _ = api.run([filename] + mypy_options)
        self._module_stack.append(
            {
                "dict-item": set(),
                "list-item": set(),
                "operator": set(),
                "assignment": set(),
                "arg-type": set(),
                "union-attr": set(),
            }
        )

        for line in result.splitlines():
            if line.endswith("[arg-type]"):
                parsed = self._parse_arg_type_information(line.strip())
                if parsed:
                    (
                        line_number,
                        argument_number,
                        function_name,
                        incompatible_type,
                        expected_type,
                    ) = parsed
                    self._module_stack[-1]["arg-type"].add(
                        (
                            line_number,
                            argument_number,
                            function_name,
                            incompatible_type,
                            expected_type,
                        )
                    )
            elif line.endswith("[assignment]"):
                parsed = self._parse_assignment_information(line.strip())
                if parsed:
                    line_number, expression_type, variable_type = parsed
                    self._module_stack[-1]["assignment"].add(
                        (line_number, expression_type, variable_type)
                    )
            elif line.endswith("[list-item]"):
                parsed = self._parse_list_item_information(line.strip())
                if parsed:
                    line_number, item_index, item_type, expected_type = parsed
                    self._module_stack[-1]["list-item"].add(
                        (line_number, item_index, item_type, expected_type)
                    )
            elif line.endswith("[operator]"):
                parsed = self._parse_operator_information(line.strip())
                if parsed:
                    line_number, operator, left_type, right_type = parsed
                    self._module_stack[-1]["operator"].add(
                        (line_number, operator, left_type, right_type)
                    )
            elif line.endswith("[union-attr]"):
                parsed = self._parse_union_attr_information(line.strip())
                if parsed:
                    line_number, item_type, attribute = parsed
                    self._module_stack[-1]["union-attr"].add((line_number, item_type, attribute))
            elif line.endswith("[dict-item]"):
                parsed = self._parse_dict_item_information(line.strip())
                if parsed:
                    (
                        line_number,
                        entry_number,
                        key_type,
                        value_type,
                        expected_key_type,
                        expected_value_type,
                    ) = parsed
                    self._module_stack[-1]["dict-item"].add(
                        (
                            line_number,
                            entry_number,
                            key_type,
                            value_type,
                            expected_key_type,
                            expected_value_type,
                        )
                    )

    @only_required_for_messages("dict-item-type-mismatch")
    def visit_dict(self, node: nodes.Dict) -> None:
        """Check for type mismatches in dictionary entries."""
        to_remove = []
        for entry in self._module_stack[-1]["dict-item"]:
            (
                line_number,
                entry_number,
                key_type,
                value_type,
                expected_key_type,
                expected_value_type,
            ) = entry
            if not (line_number == node.lineno and (0 <= entry_number < len(node.items))):
                continue
            key_node, value_node = node.items[entry_number]
            if not (
                self._normalize_pytype(key_node.pytype()) == key_type
                and self._normalize_pytype(value_node.pytype()) == value_type
            ):
                continue
            self.add_message(
                "dict-item-type-mismatch",
                node=node,
                line=line_number,
                args=(entry_number, key_type, value_type, expected_key_type, expected_value_type),
            )
            to_remove.append(entry)

        for entry in to_remove:
            self._module_stack[-1]["dict-item"].remove(entry)

    @only_required_for_messages("list-item-type-mismatch")
    def visit_list(self, node: nodes.List) -> None:
        """Check for type mismatches in list items."""
        to_remove = []
        for entry in self._module_stack[-1]["list-item"]:
            line_number, item_index, item_type, expected_type = entry

            if not (line_number == node.lineno and (0 <= item_index < len(node.elts))):
                continue
            element_node = node.elts[item_index]
            if self._normalize_pytype(element_node.pytype()) != item_type:
                continue
            self.add_message(
                "list-item-type-mismatch",
                node=element_node,
                line=line_number,
                args=(item_index, item_type, expected_type),
            )
            to_remove.append(entry)

        for entry in to_remove:
            self._module_stack[-1]["list-item"].remove(entry)

    @only_required_for_messages("unsupported-operand-types")
    def visit_binop(self, node: nodes.BinOp) -> None:
        """Check for unsupported operand types in binary operations."""
        to_remove = []
        for entry in self._module_stack[-1]["operator"]:
            line_number, operator, left_type, right_type = entry

            if not (line_number == node.lineno and node.op == operator):
                continue

            left_node, right_node = node.left, node.right

            if not (
                self._normalize_pytype(left_node.pytype()) == left_type
                and self._normalize_pytype(right_node.pytype()) == right_type
            ):
                continue

            self.add_message(
                "unsupported-operand-types",
                node=node,
                line=line_number,
                args=(operator, left_type, right_type),
            )
            to_remove.append(entry)

        for entry in to_remove:
            self._module_stack[-1]["operator"].remove(entry)

    @only_required_for_messages("incompatible-argument-type")
    def visit_call(self, node: nodes.Call) -> None:
        """Check for type mismatches in function call arguments."""
        to_remove = []
        for entry in self._module_stack[-1]["arg-type"]:
            line_number, argument_number, function_name, incompatible_type, expected_type = entry

            if not (line_number == node.lineno and 0 <= argument_number - 1 < len(node.args)):
                continue

            if isinstance(node.func, astroid.Name) and node.func.name != function_name:
                continue
            argument_node = node.args[argument_number - 1]
            if self._normalize_pytype(argument_node.pytype()) != incompatible_type:
                continue
            self.add_message(
                "incompatible-argument-type",
                node=argument_node,
                line=line_number,
                args=(argument_number, function_name, incompatible_type, expected_type),
            )
            to_remove.append(entry)

        for entry in to_remove:
            self._module_stack[-1]["arg-type"].remove(entry)

    @only_required_for_messages("union-attr-error")
    def visit_attribute(self, node: nodes.Attribute) -> None:
        """Check for attribute access on incorrect union types."""
        to_remove = []
        for entry in self._module_stack[-1]["union-attr"]:
            line_number, item_type, attribute = entry
            if line_number != node.lineno and node.attrname != attribute:
                continue
            self.add_message(
                "union-attr-error",
                node=node,
                line=line_number,
                args=(item_type, attribute),
            )
            to_remove.append(entry)

        for entry in to_remove:
            self._module_stack[-1]["union-attr"].remove(entry)

    @only_required_for_messages("incompatible-assignment")
    def visit_annassign(self, node: nodes.AnnAssign) -> None:
        """Check for type mismatches in annotated assignments."""
        to_remove = []
        for entry in self._module_stack[-1]["assignment"]:
            line_number, expression_type, variable_type = entry

            if not (line_number == node.lineno and node.annotation.name == variable_type):
                continue

            self.add_message(
                "incompatible-assignment",
                node=node,
                line=line_number,
                args=(expression_type, variable_type),
            )
            to_remove.append(entry)

        for entry in to_remove:
            self._module_stack[-1]["assignment"].remove(entry)

    def leave_module(self, node: nodes.Module) -> None:
        """Clean up the module stack when leaving a module."""
        self._module_stack.pop()

    def _parse_assignment_information(self, message: str) -> Optional[tuple[int, str, str]]:
        """Parse Mypy assignment error messages into structured data."""
        pattern = r"^\S+:(\d+): error: Incompatible types in assignment \(expression has type \"([^\"]+)\", variable has type \"([^\"]+)\"\)"
        match = re.search(pattern, message)
        if match:
            line_number = int(match.group(1))
            expression_type = match.group(2)
            variable_type = match.group(3)
            return line_number, expression_type, variable_type
        return None

    def _parse_arg_type_information(self, message: str) -> Optional[tuple[int, int, str, str, str]]:
        """Parse Mypy argument type error messages into structured data."""
        pattern = r"^\S+:(\d+): error: Argument (\d+) to \"([^\"]+)\" has incompatible type \"([^\"]+)\"; expected \"([^\"]+)\""
        match = re.search(pattern, message)
        if match:
            line_number = int(match.group(1))
            argument_number = int(match.group(2))
            function_name = match.group(3)
            incompatible_type = match.group(4)
            expected_type = match.group(5)
            return line_number, argument_number, function_name, incompatible_type, expected_type
        return None

    def _parse_list_item_information(self, message: str) -> Optional[tuple[int, int, str, str]]:
        """Parse Mypy list item error messages into structured data."""
        pattern = r"^\S+:(\d+): error: List item (\d+) has incompatible type \"([^\"]+)\"; expected \"([^\"]+)\""
        match = re.search(pattern, message)
        if match:
            line_number = int(match.group(1))
            item_index = int(match.group(2))
            item_type = match.group(3)
            expected_type = match.group(4)
            return line_number, item_index, item_type, expected_type
        return None

    def _parse_operator_information(self, message: str) -> Optional[tuple[int, str, str, str]]:
        """Parse Mypy operator error messages into structured data."""
        pattern = r"^\S+:(\d+): error: Unsupported operand types for (\S+) \(\"([^\"]+)\" and \"([^\"]+)\"\)"
        match = re.search(pattern, message)
        if match:
            line_number = int(match.group(1))
            operator = match.group(2)
            left_type = match.group(3)
            right_type = match.group(4)
            return line_number, operator, left_type, right_type
        return None

    def _parse_union_attr_information(self, message: str) -> Optional[tuple[int, str, str]]:
        """Parse Mypy union attribute error messages into structured data."""
        pattern = (
            r"^\S+:(\d+): error: Item \"([^\"]+)\" of \"[^\"]+\" has no attribute \"([^\"]+)\""
        )
        match = re.search(pattern, message)
        if match:
            line_number = int(match.group(1))
            item_type = match.group(2)
            attribute = match.group(3)
            return line_number, item_type, attribute
        return None

    def _parse_dict_item_information(
        self, message: str
    ) -> Optional[tuple[int, int, str, str, str, str]]:
        """Parse Mypy dictionary item error messages into structured data."""
        pattern = r"^\S+:(\d+): error: Dict entry (\d+) has incompatible type \"([^\"]+)\": \"([^\"]+)\"; expected \"([^\"]+)\": \"([^\"]+)\""
        match = re.search(pattern, message)
        if match:
            line_number = int(match.group(1))
            entry_number = int(match.group(2))
            key_type = match.group(3)
            value_type = match.group(4)
            expected_key_type = match.group(5)
            expected_value_type = match.group(6)
            return (
                line_number,
                entry_number,
                key_type,
                value_type,
                expected_key_type,
                expected_value_type,
            )
        return None

    def _normalize_pytype(self, pytype: str) -> str:
        """Normalize a Python type string for consistent comparison."""
        if pytype.startswith("builtins."):
            return pytype[len("builtins.") :]
        return pytype


def register(linter: PyLinter) -> None:
    """Register the StaticTypeChecker with pylint."""
    linter.register_checker(StaticTypeChecker(linter))
