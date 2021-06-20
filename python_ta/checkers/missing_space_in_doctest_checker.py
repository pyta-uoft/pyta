import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class MissingSpaceInDoctestChecker(BaseChecker):
    __implements__ = IAstroidChecker

    name = 'missing_space_in_doctest'
    msgs = {'E9973': ('Space missing in doctest on line %s',
                      'missing-space-in-doctest',
                      'Used when a doctest is missing a space before the code to be executed')
            }
    # This is important so that your checker is executed before others
    priority = -1

    @check_messages("missing-space-in-doctest")
    def visit_functiondef(self, node: astroid.FunctionDef) -> None:
        ...


def register(linter):
    """Required method to auto register this checker"""
    linter.register_checker(MissingSpaceInDoctestChecker(linter))
