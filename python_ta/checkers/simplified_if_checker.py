"""
checker for using constant value in a conditional statement
"""
import astroid

from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class SimplifiedIfChecker(BaseChecker):
    __implements__ = IAstroidChecker

    name = 'simplified-if'

    msgs = {'E9906': ('If statement can be replaced with return exp'
                      , 'simplified-if'
                      , 'The if statement can be simplified be returning what is equivalent to true '
                        'in terms of the expression checking for')}

    # this is important so that your checker is executed before others
    priority = -1

    def _check_bool_return(self, node):
        """
        Checks whether the value returned in a return node is a boolean value.
        Precondition: node is of type astroid.Return
        :param node: The return node which is being checked
        :return: True if the return value is True/False and False otherwise
        """
        if isinstance(node.value, astroid.Const):
            constant = node.value
            if constant.value == False or constant.value == True:
                return True
        return False

    def _check_requirements(self, node):
        """
        Checks whether the current if statement has any elif branches
        Precondition: Node is an if statement node.
        :param node: the node we are checking the requirements for.
        :return: True if the current if statement has no elif branches and False otherwise
        """
        if len(node.orelse) != 1 or len(node.body) != 1:
            return False

        # Check if both branches can be reduced.
        if_body = node.body[0]
        else_body = node.orelse[0]

        if isinstance(if_body, astroid.Return) and isinstance(else_body, astroid.Return):
            if self._check_bool_return(if_body) and self._check_bool_return(else_body):
                return True
        return False

    def _check_simplified_if(self, node):
        """
        Precondition: node is a condition in an if statement
        """
        if self._check_requirements(node):
            return True

    @check_messages("simplified-if")
    def visit_if(self, node):
        if self._check_simplified_if(node):
            self.add_message('simplified-if', node=node.test)


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(SimplifiedIfChecker(linter))
