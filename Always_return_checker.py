"""checker for always returning in a loop.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class AlwaysReturnChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'always_return'
    msgs = {'E9996': ('Always returning true/false in loop on line %s',
                      'always_returning_in_a_loop',
                      'Used when you always return ture or false in a loop, '
                      'this may cause the loop only runs once.'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    @check_messages("always_returning_in_a_loop")
    def helper_fuc(self, node):
        flag = True
        body_length = len(node.body)
        # If the node is just a single statement or a sequence of statement,
        # check whether it's a return statement or whether one of them is a
        # return statement
        if body_length > 0 and any([isinstance(child, astroid.Return) for child in node.body]):
            args = "{}".format(node.lineno)
            self.add_message("always_returning_in_a_loop", node=node, args=args)
        # If it's an if statement, check each branch separately, and only
        # return True if every branch has an explicit return.
        for branch in node.body:
            # check if the current branch is astroid.If
            if isinstance(branch, astroid.If):
                # Return False if there is no return in this branch
                if not any([isinstance(child, astroid.Return) for child in (
                        branch.body + branch.orelse)]):
                    flag = False
                # set first_branch
                if branch.orelse and isinstance(branch.orelse[0], astroid.If):
                    first_branch = branch.orelse[0]
                elif branch.orelse:
                    # Return False if there is no return in else branch
                    if not any([isinstance(child, astroid.Return) for child in (
                            branch.orelse)]):
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
            # If it's a loop, check the body of the loop.
            if isinstance(branch, astroid.For) or isinstance(branch, astroid.While):
                return self.helper_fuc(branch)
        # check the flag and decide whether there is error
        if flag:
            args = "{}".format(node.lineno)
            self.add_message("always_returning_in_a_loop", node=node, args=args)

    def visit_for(self, node):
        self.helper_fuc(node)

    def visit_while(self, node):
        self.helper_fuc(node)

def register(linter):
    linter.register_checker(AlwaysReturnChecker(linter))
