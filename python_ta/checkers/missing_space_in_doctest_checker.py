"""Checker for E9973 missing-space-in-doctest"""
import astroid

from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages

from typing import Match, Union, Optional

import re

DOCTEST = ">>>"


class MissingSpaceInDoctestChecker(BaseChecker):
    __implements__ = IAstroidChecker

    name = 'missing_space_in_doctest'
    msgs = {'E9973': ('Space missing after >>> in the docstring of function "%s."',
                      'missing-space-in-doctest',
                      'Used when a doctest is missing a space before the code to be executed')
            }
    # This is important so that your checker is executed before others
    priority = -1

    @check_messages("missing-space-in-doctest")
    def visit_functiondef(self, node: astroid.FunctionDef) -> None:
        """Visit a function definition"""
        docstring = node.doc

        if docstring is not None:
            start_line = node.lineno
            lines = docstring.split('\n')

            for line_no, line in enumerate(lines):
                if self._invalid_doctest(line):
                    self.add_message(
                        'missing-space-in-doctest',
                        node=node,
                        args=node.name,
                        line=line_no + start_line + 1
                    )

    # Helper Function
    def _invalid_doctest(self, doc: str) -> Union[bool, Optional[Match[str]]]:
        """Return whether the docstring line contains an invalid doctest
        """
        start_index = doc.find(DOCTEST)
        contains_doctest = start_index != -1
        if contains_doctest:
            if len(doc) > 3:
                match = re.match("\s*>>>\w", doc)
                return match
            return True  # Otherwise, the doctest isn't followed by any character
        return False


def register(linter):
    """Required method to auto register this checker"""
    linter.register_checker(MissingSpaceInDoctestChecker(linter))
