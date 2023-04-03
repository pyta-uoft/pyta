"""Checker for E9973 missing-space-in-doctest"""
import re
from typing import Match, Optional, Union

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages

DOCTEST = ">>>"


class MissingSpaceInDoctestChecker(BaseChecker):
    name = "missing_space_in_doctest"
    msgs = {
        "E9973": (
            'Space missing after >>> in the docstring of "%s."',
            "missing-space-in-doctest",
            "Used when a doctest is missing a space before the code to be executed",
        )
    }
    # This is important so that your checker is executed before others
    priority = -1

    @only_required_for_messages("missing-space-in-doctest")
    def visit_functiondef(self, node: nodes.FunctionDef) -> None:
        """Visit a function definition"""
        self._check_docstring(node)

    @only_required_for_messages("missing-space-in-doctest")
    def visit_classdef(self, node: nodes.ClassDef) -> None:
        """Visit a Class definition"""
        self._check_docstring(node)

    @only_required_for_messages("missing-space-in-doctest")
    def visit_module(self, node: nodes.Module) -> None:
        """Visit a Module definition"""
        self._check_docstring(node)

    # Helper Functions
    def _check_docstring(self, node) -> None:
        """Go through the docstring of the respective node type"""
        if node.doc_node is not None:
            docstring = node.doc_node.value or ""
            start_line = node.lineno + 1
            lines = docstring.split("\n")

            for line_no, line in enumerate(lines):
                if self._has_invalid_doctest(line):
                    self.add_message(
                        "missing-space-in-doctest",
                        node=node,
                        args=node.name,
                        line=line_no + start_line,
                    )

    def _has_invalid_doctest(self, doc: str) -> Union[bool, Optional[Match[str]]]:
        """Return whether the docstring line contains an invalid doctest"""
        start_index = doc.find(DOCTEST)
        contains_doctest = start_index != -1
        if contains_doctest and len(doc) == 3:
            return True  # The doctest isn't followed by any character
        match = re.match(r"\s*>>>\w", doc)
        return match


def register(linter):
    """Required method to auto register this checker"""
    linter.register_checker(MissingSpaceInDoctestChecker(linter))
