"""checker for always returning in a loop.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class AlwaysReturnChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'always_return'
    msgs = {'E9996': ('Always returning an object or none in the loop on line %s',
                      'always_returning_in_a_loop',
                      'Used when you always return an object or none in a loop, '
                      'this may cause the loop only runs once.'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    @check_messages("always_returning_in_a_loop")
    def helper_fuc(self, node):
        # Check if the node is a return statement
        if isinstance(node, astroid.Return):
            args = "{}".format(node.lineno)
            self.add_message("always_returning_in_a_loop", node=node, args=args)
        # check if the current branch is astroid.If
        if isinstance(node, astroid.If):
            flag = True
            if not any([isinstance(child, astroid.Return) for child in (
                    node.body + node.orelse)]):
                flag = False
            # set first_branch
            if node.orelse and isinstance(node.orelse[0], astroid.If):
                first_branch = node.orelse[0]
            elif node.orelse:
                # Return False if there is no return in else branch
                if not any([isinstance(child, astroid.Return) for child in (
                        node.orelse)]):
                    flag = False
                first_branch = "end"
            else:
                first_branch = "end"
            # check if every branch has a explicit return
            while first_branch != "end":
                # Return False if there is no return in this branch
                if not any([isinstance(child, astroid.Return) for child in (
                        first_branch.body + first_branch.orelse)]):
                    flag = False
                if first_branch.orelse and isinstance(first_branch.orelse[0],
                    astroid.If):
                    first_branch = first_branch.orelse[0]
                # Return False if there is no return in else branch
                elif first_branch.orelse:
                    if not any([isinstance(child, astroid.Return) for child in (
                            first_branch.orelse)]):
                        flag = False
                else:
                    first_branch = "end"
                # check the flag and decide whether there is error
            if flag:
                args = "{}".format(node.lineno)
                self.add_message("always_returning_in_a_loop", node=node, args=args)
        # If it's a loop, check the body of the loop.
        if isinstance(node, astroid.For) or isinstance(node, astroid.While):
            for child in node.body:
                self.helper_fuc(child)

    def visit_for(self, node):
        return self.helper_fuc(node)

    def visit_while(self, node):
        return self.helper_fuc(node)


def register(linter):
    linter.register_checker(AlwaysReturnChecker(linter))
