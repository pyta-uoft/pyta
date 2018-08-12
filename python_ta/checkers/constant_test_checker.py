"""
checker for using constant value in a conditional statement
"""
import astroid

from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class UsingConstantTestChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'using-constant-test'

    msgs = {'E9902': ('The condition includes at least one constant '
                      'which will always return True (if non-zero constant) or always '
                      'return False (if zero)'
                      , 'using-constants-test'
                      , 'Conditional statements should depend on a variable not a constant value.'
                        'This is usually not what the user intended to do')}

    # this is important so that your checker is executed before others
    priority = -1

    def _check_all_constants(self, node) -> bool:
        """
        Precondition: node is a condition in an if statement
        Returns true if at least one of the values in this node is a constant
        Returns false otherwise
        """
        if isinstance(node, astroid.Const):
            return True
        elif isinstance(node, astroid.BinOp):
            return self._check_all_constants(node.left) and self._check_all_constants(node.right)
        elif isinstance(node, astroid.UnaryOp):
            return self._check_all_constants(node.operand)
        elif isinstance(node, astroid.BoolOp):
            return all(self._check_all_constants(v) for v in node.values)
        else:
            return False


    @check_messages("using-constants-test")
    def visit_if(self, node):
        if self._check_all_constants(node.test):
            self.add_message('using-constants-test', node=node.test)


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(UsingConstantTestChecker(linter))
