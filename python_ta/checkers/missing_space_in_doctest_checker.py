"""Checker for E9973 missing-space-in-doctest"""
import astroid
import re

from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages

from typing import List


class MissingSpaceInDoctestChecker(BaseChecker):
    __implements__ = IAstroidChecker

    name = 'missing_space_in_doctest'
    msgs = {'E9973': ('Space missing in doctest(s) in the docstring of function "%s."',
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
            doctests = self._find_doctests(docstring)
            if doctests != []:
                if any(not self._has_space(docstring, doctest) for doctest in doctests):
                    self.add_message(
                        'missing-space-in-doctest', node=node, args=node.name
                    )

    # Helper Functions
    def _find_doctests(self, doc: str) -> List[int]:
        """Return a list of the indices of the doctests found in the docstring

        Returns [] if no doctests are found in the docstring
        """
        doctest = ">>>"
        matches = re.finditer(doctest, doc)
        return [m.start() for m in matches]

    def _has_space(self, doc: str, doctest_index: int) -> bool:
        """Return whether the doctest is followed by a space"""
        doctest = doc[doctest_index:doctest_index + 4]
        return doctest[-1] == " "


def register(linter):
    """Required method to auto register this checker"""
    linter.register_checker(MissingSpaceInDoctestChecker(linter))
