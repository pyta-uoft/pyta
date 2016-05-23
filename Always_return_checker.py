"""checker for always returning in a loop.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import base
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class AlwaysReturnChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'always_return'
    msgs = {'E9997': ('Always returning true/false in loop on line %s',
                      'always_returning_in_a_loop',
                      'Used when you always return ture or false in a loop, '
                      'this may cause the loop only runs once.'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    @check_messages("always_returning_in_a_loop")
    def visit_for(self, node):
        length = len(node.body)
        first_branch = node.body[0]
        # If the node is just a single statement, check whether it's a return
        # statement.
        if length == 1 and first_branch.is_statement:
            if isinstance(first_branch, astroid.Return):
                args = "{}".format(node.lineno)
                self.add_message("always_returning_in_a_loop", node=node, args=args)
        # If it's a sequence of statements, check whether one of them is a
        # return statement
        if length > 1 and all([child.is_statement for child in node.body]):
            if any([isinstance(child, astroid.Return) for child in node.body]):
                args = "{}".format(node.lineno)
                self.add_message("always_returning_in_a_loop", node=node, args=args)
        # If it's an if statement, check each branch separately, and only
        # return True if every branch has an explicit return.
        if length == 1 and isinstance(first_branch, astroid.If):
            if any([isinstance(child, astroid.Return) for child in first_branch.body]):
                args = "{}".format(node.lineno)
                self.add_message("always_returning_in_a_loop", node=node, args=args)
        # If it's a loop, check the body of the loop.
        if isinstance(first_branch, astroid.For):
            return self.visit_for(first_branch)
        if isinstance(first_branch, astroid.While):
            return self.visit_while(first_branch)

    def visit_while(self, node):
        length = len(node.body)
        first_branch = node.body[0]
        # If the node is just a single statement, check whether it's a return
        # statement.
        if length == 1 and first_branch.is_statement:
            if isinstance(first_branch, astroid.Return):
                args = "{}".format(node.lineno)
                self.add_message("always_returning_in_a_loop", node=node, args=args)
        # If it's a sequence of statements, check whether one of them is a
        # return statement
        if length > 1 and all([child.is_statement for child in node.body]):
            if any([isinstance(child, astroid.Return) for child in node.body]):
                args = "{}".format(node.lineno)
                self.add_message("always_returning_in_a_loop", node=node, args=args)
        # If it's an if statement, check each branch separately, and only
        # return True if every branch has an explicit return.
        if length == 1 and isinstance(first_branch, astroid.If):
            if any([isinstance(child, astroid.Return) for child in first_branch.body]):
                args = "{}".format(node.lineno)
                self.add_message("always_returning_in_a_loop", node=node, args=args)
        # If it's a loop, check the body of the loop.
        if isinstance(first_branch, astroid.For):
            return self.visit_for(first_branch)
        if isinstance(first_branch, astroid.While):
            return self.visit_while(first_branch)


def register(linter):
    linter.register_checker(AlwaysReturnChecker(linter))
