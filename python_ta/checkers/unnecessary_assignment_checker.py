"""
Checker for unnecessary assignment to a variable.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from typing import Any
from typing import List


class UnnecessaryAssignmentChecker(BaseChecker):
    """Checker for unnecessary assignment to variables in several cases."""
    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'unnecessary_assignment'
    msgs = {'E9917': ('This variable assignment is unnecessary.',
                      'Used when there is an assignment statement that could be '
                      'removed without changing the meaning of the program.'),
            }

    # this is important so that your checker is executed before others. It seems all
    # the checkers have the same priority though.
    priority = -1

    def _check_unnecessary_assignment(self, node: Any)-> List[Any]:
        """Returns a list of nodes within the function that are instances of unnecessary assignment."""

        # This is the list of lists(groups) of nodes that inhabit the same "body" . ie the nodes
        # are not separated by any branching.
        groups = self._split_into_groups(node)

        # This initializes the list of nodes where unnecessary assignment has taken place.
        allerrors = []

        # This for loop iterates over each of the groups of unbranched nodes.
        for group in groups:

            # This errors variable will be the variable that will be a list of errors for the given group
            # of the current iteration.
            errors = self._check_group(node, group)

            # The following loop will effectively add each of the errors for the current group to the total errors.
            for error in errors:
                allerrors.append(error)

        return allerrors

    def _split_into_groups(self, node: Any) -> List[List]:
        """
        Given a function node, recursively creates a list of lists;
        where each list is a series of nodes that would execute for a given path of execution
        the computer would take through the function. The returned list of lists is
        effectively a list of every possible path of execution.
        """

        # This is initializes the groups of nodes.
        groups = []

        # "unbranchednodes" is the name for the list of function body nodes. The uppermost level of the body,
        # without any branching.
        unbranchednodes = []

        if not isinstance(node, astroid.If):

            # This will be the list of nodes that should be excluded from "unbranchednodes".
            # Includes If nodes and all their children.
            removelist = []

            # All the If nodes. For use in recursion.
            iflist = []

            # This for loop will iterate for every If node within the function.
            for blocktwo in node.nodes_of_class(astroid.If):

                removelist.append(blocktwo)
                iflist.append(blocktwo)

                # This for loop will iterate through all the children of the current If node.
                for item in blocktwo.nodes_of_class(astroid.ALL_NODE_CLASSES):
                    # This will add the given child node of the If node to the removelist.
                    if item not in removelist:
                        removelist.append(item)

            # This will populate the unbranchesnodes list with all the nodes outside of branching.
            for block in node.nodes_of_class(astroid.ALL_NODE_CLASSES):
                if block not in removelist:
                    unbranchednodes.append(block)

            groups.append(unbranchednodes)

            while not iflist == []:
                further = self._split_into_groups(iflist[0])
                for item in further:
                    groups.append(item)
                iflist.pop(0)

        elif isinstance(node, astroid.If):
            bodynodes = []
            orelsenodes = []
            for element in node.body:
                if isinstance(element, astroid.If):
                    furthertwo = self._split_into_groups(element)
                    for item in furthertwo:
                        groups.append(item)
                else:
                    bodynodes.append(element)
            for elementtwo in node.orelse:
                if isinstance(elementtwo, astroid.If):
                    furtherthree = self._split_into_groups(elementtwo)
                    for item in furtherthree:
                        groups.append(item)
                else:
                    orelsenodes.append(elementtwo)

            groups.append(bodynodes)
            groups.append(orelsenodes)

        return groups

    def _check_group(self, node: Any, group: List) -> List[Any]:
        """
        This function will check the given group of nodes within the context
        of the function node to check for unnecessary assignment.
        """

        values = {}  # creates a 'notetaker' for when values are assigned and used.

        for var in node.locals:  # initializes the values list with all the local variables.
            values[var] = None

        errors = []  # the list of problematic nodes

        for block in node.nodes_of_class(astroid.ALL_NODE_CLASSES):
            if block in group:
                if not isinstance(block.parent, astroid.FunctionDef):
                    # the reason we care if the parent is the FunctionDef is because the only Name
                    # node that this will be the case for is the Name node for the .return field of the FunctionDef
                    # which isn't technically part of the function, it just describes the return type, not value.

                    if isinstance(block, astroid.AssignName):
                        # here we are checking if the given node is one where assignment takes place.

                        if block.name in values and values[block.name] is not None and not isinstance(block.parent, astroid.AugAssign) and isinstance(values[block.name], astroid.AssignName):
                            # if it is already in the values list and being reassigned before use then there
                            # is unnecessary assignment and we should add it to errors.
                            # KEY NOTE, this is unless it is part of an augmented assignment!
                            values[block.name] = block
                            errors.append(values[block.name].parent)  # this will add the parent node
                            # so the whole line is highlighted

                        elif block.name in values:
                            # Either it hasn't been assigned to yet or it has been used.
                            values[block.name] = block

                    elif isinstance(block, astroid.Name) and block.name in values:
                        # here we check if the value is being used.
                        values[block.name] = block

            for val in values:
                # this will check at the end if there were values unused.
                if isinstance(values[val], astroid.AssignName):
                    errors.append(values[val].parent)

            return errors

    # pass in message symbol as a parameter of check_messages
    @check_messages("unnecessary-assignment")
    def visit_functiondef(self, node: Any):
        """Visits nodes of functionDef type in file to check unnecessary assignment."""
        checks = self._check_unnecessary_assignment(node)
        if not checks == []:
            # this will return the problematic node.
            for item in checks:
                self.add_message('unnecessary-assignment', node=item)


def register(linter):
    """Registers linter."""
    linter.register_checker(UnnecessaryAssignmentChecker(linter))
