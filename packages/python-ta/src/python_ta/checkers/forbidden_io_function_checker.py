"""Checker for use of I/O functions."""

from re import sub
from typing import Union

from astroid import BoundMethod, nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages, safe_infer
from pylint.lint import PyLinter

from python_ta.utils import _is_in_main

FORBIDDEN_BUILTIN = ["input", "print", "open"]


class IOFunctionChecker(BaseChecker):
    """A checker class to report on the use of disallowed I/O functions.

    Use options to specify the forbidden I/O functions and the allowed I/O functions."""

    name = "IO_Function"
    msgs = {
        "E9998": (
            "Used input/output function %s",
            "forbidden-IO-function",
            'Used when you use the I/O functions "print", "open" or "input" or other config-specified forbidden '
            "functions. These functions should not be used except where specified by your instructor.",
        )
    }
    options = (
        (
            "forbidden-io-functions",
            {
                "default": FORBIDDEN_BUILTIN,
                "type": "csv",
                "metavar": "<builtin function names>",
                "help": "List of I/O function names and method qualified names that should not be used.",
            },
        ),
        (
            "allowed-io",
            {
                "default": (),
                "type": "csv",
                "metavar": "<forbidden io>",
                "help": "Functions where an I/O function may be used.",
            },
        ),
    )

    @only_required_for_messages("forbidden-IO-function")
    def visit_call(self, node: nodes.Call) -> None:
        if (name := self._resolve_qualname(node)) in self.linter.config.forbidden_io_functions:
            scope = node.scope()
            scope_parent = scope.parent

            if (
                isinstance(scope_parent, nodes.ClassDef)
                and isinstance(scope, nodes.FunctionDef)
                and (scope_parent.name + "." + scope.name) not in self.linter.config.allowed_io
            ):
                self.add_message("forbidden-IO-function", node=node, args=name)
            elif (
                isinstance(scope_parent, nodes.Module)
                and isinstance(scope, nodes.FunctionDef)
                and scope.name not in self.linter.config.allowed_io
            ):
                self.add_message("forbidden-IO-function", node=node, args=name)
            elif isinstance(scope, nodes.Module) and not _is_in_main(node):
                self.add_message("forbidden-IO-function", node=node, args=name)

    @staticmethod
    def _resolve_qualname(node: nodes.Call) -> Union[str, None]:
        """Resolves the qualified name for function and method calls"""
        if (inferred_definition := safe_infer(node.func)) is not None:
            if isinstance(inferred_definition, (BoundMethod, nodes.FunctionDef)):
                return sub(r"^[^.]*\.", "", inferred_definition.qname())
        if isinstance(node.func, nodes.Name):
            return node.func.name
        return None


def register(linter: PyLinter) -> None:
    """Required method to auto-register this checker to the linter"""
    linter.register_checker(IOFunctionChecker(linter))
