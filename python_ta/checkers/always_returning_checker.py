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
    def helper_func(self, node, args):
        # Check if the node is a return statement
        if isinstance(node, astroid.Return):
            self.add_message("always_returning_in_a_loop", node=node, args=args)
        # set the flag = True.
        # Once there is not an explicit return, flag = false
        flag = True
        # check if the node a if statement
        if isinstance(node, astroid.If):
            # check the body of the if node
            for child in node.body:
                if isinstance(child, astroid.If):
                    return self.helper_func(child, args)
            # set first_branch
            if node.orelse and isinstance(node.orelse[0], astroid.If):
                first_branch = node.orelse[0]
            elif node.orelse:
                # Return False if there is no return in else branch
                if not any([isinstance(child, astroid.Return) for child in (
                        node.orelse)]):
                    flag = False
                first_branch = "end"
                for child in node.orelse:
                    if isinstance(child, astroid.If):
                        return self.helper_func(child, args)
            else:
                first_branch = "end"
            # check if every branch has a explicit return
            while first_branch != "end":
                # Return False if there is no return in this branch
                if not any([isinstance(child, astroid.Return) for child in (
                        first_branch.body + first_branch.orelse)]):
                    flag = False
                    first_branch = "end"
                # deal with the condition of nested if
                for child in first_branch.body:
                    if isinstance(child, astroid.If):
                        return self.helper_func(child, args)
                if first_branch.orelse and isinstance(first_branch.orelse[0],
                                                      astroid.If):
                    first_branch = first_branch.orelse[0]
                    # deal with the condition of nested if
                    for child in first_branch.orelse.body:
                        if isinstance(child, astroid.If):
                            return self.helper_func(child, args)
                # Return False if there is no return in else branch
                elif first_branch.orelse:
                    if not any([isinstance(child, astroid.Return) for child in (
                            first_branch.orelse)]):
                        flag = False
                    for child in first_branch.orelse:
                        if isinstance(child, astroid.If):
                            return self.helper_func(child, args)
                    first_branch = "end"
                else:
                    first_branch = "end"
            # check the flag and decide whether there is error
            if flag:
                self.add_message("always_returning_in_a_loop", node=node,
                                 args=args)
        # If it's a loop, check the body of the loop.
        if isinstance(node, astroid.For) or isinstance(node, astroid.While):
            for child in (node.body):
                self.helper_func(child, args=node.lineno)

    def visit_for(self, node):
        args = "{}".format(node.lineno)
        return self.helper_func(node, args)

    def visit_while(self, node):
        args = "{}".format(node.lineno)
        return self.helper_func(node, args)


def register(linter):
    linter.register_checker(AlwaysReturnChecker(linter))
