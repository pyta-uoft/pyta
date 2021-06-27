"""Checker for E9973 missing-space-in-doctest"""
import astroid

from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages

DOCTEST = ">>>"


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
            start_line = node.lineno
            lines = docstring.split('\n')
            line_no = start_line

            for line in lines:
                line_no += 1
                if self._has_doctest(line):
                    if not self._has_space(line):
                        self.add_message(
                            'missing-space-in-doctest',
                            node=node,
                            args=node.name,
                            line=line_no
                        )

    # Helper Functions
    def _has_doctest(self, doc: str) -> bool:
        """Return whether the docstring line contains a doctest
        """
        return doc.find(DOCTEST) != -1

    def _has_space(self, doc: str) -> bool:
        """Return whether the docstring line containing a doctest is followed by a space
        """
        start_index = doc.find(DOCTEST)
        if len(doc) > 3:
            end_index = start_index + 3
            return doc[end_index] == " "
        return False  # Otherwise, the doctest isn't followed by any character


def register(linter):
    """Required method to auto register this checker"""
    linter.register_checker(MissingSpaceInDoctestChecker(linter))
