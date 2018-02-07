"""
checker for using constant value in a conditional statement
"""
import astroid

from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class UsingStructureTestChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'using-structure-test'

    msgs = {'E9901': ('Structures have a constant true value, meaning the same branch will always be executed '
                      '(and the other branch does not have a purpose).'
                      , 'using-structure-test'
                      , 'Conditional statements should depend on a variable not a constant value.'
                        'This is usually not what the user intended to do')}

    #Collections always return True

    # this is important so that your checker is executed before others
    priority = -1

    def _check_collection(self, node):
        """
        Precondition: node is a condition in an if statement
        Returns true if all the node is a structure/collection of values
        Returns false otherwise
        """
        if isinstance(node, astroid.List) or isinstance(node, astroid.Tuple) or isinstance(node, astroid.Dict) or \
                isinstance(node, astroid.Set):
            return True

    @check_messages("using-structures-test")
    def visit_if(self, node):
        if self._check_collection(node.test):
            self.add_message('using-structure-test', node=node.test)


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(UsingStructureTestChecker(linter))
