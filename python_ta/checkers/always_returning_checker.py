"""checker for always returning in a loop.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class AlwaysReturnChecker(BaseChecker):

    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'always_returning'
    # use dashes for connecting words in message symbol
    msgs = {'E9996': ('Always returning an object or none in the loop at this line',
                      'always-returning-in-a-loop',
                      'Used when you always return an object or none in a loop, '
                      'this may cause the loop to only run once.'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    def _check_always_return(self, node):
        """Return whether this node always returns when executed."""
        # If the node is a return statement, it always returns
        if isinstance(node, astroid.Return):
            return True

        # If it's a loop, check the body of the loop.
        elif isinstance(node, astroid.For) or isinstance(node, astroid.While):
            return any(self._check_always_return(child) for child in node.body)

        # If it's an if statement, first check its body, then its branches.
        elif isinstance(node, astroid.If):
            # Otherwise, first check the body of the if node
            if_body_returns = any(
                self._check_always_return(child) for child in node.body)

            # Then check other branches.
            # node.orelse either has a list of statements (else branch),
            # or a single If (elif, possibly nested).
            if len(node.orelse) == 1 and isinstance(node.orelse[0], astroid.If):
                branches_return = self._check_always_return(node.orelse[0])
            else:
                # Inside the else branch; check if one statement returns.
                branches_return = any(
                    self._check_always_return(child) for child in node.orelse)

            return if_body_returns and branches_return

        # Any other node is considered to not return
        else:
            return False

    # pass in message symbol as a parameter of check_messages
    @check_messages("always-returning-in-a-loop")
    def visit_for(self, node):
        if self._check_always_return(node):
            self.add_message('always-returning-in-a-loop', node=node)

    @check_messages("always-returning-in-a-loop")
    def visit_while(self, node):
        if self._check_always_return(node):
            self.add_message("always-returning-in-a-loop", node=node)


def register(linter):
    linter.register_checker(AlwaysReturnChecker(linter))
