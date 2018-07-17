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
    # use dashes for connecting words in message symbol. C for the message-id is because
    #  I believe this to be a convention issue.
    msgs = {'E9917': ('There is an unnecessary assignment within the function',
                      'unnecessary-assignment',
                      'Used when there is an assignment that does not affect the '
                      'function\'s return value'),
            }

    # this is important so that your checker is executed before others. It seems all
    # the checkers have the same priority though.
    priority = -1

    def _check_unnecessary_assignment(self, node):
        """Return whether this function has an instance of unnecessary assignment."""

        groups = self._split_into_groups(node)
        allerrors = []

        for group in groups:
            errors = self._check_group(node, group)
            for error in errors:
                allerrors.append(error)

        return allerrors


    def _split_into_groups(self, node: Any) -> List[List]:
        """Takes the given node and breaks it down into separate groups
        of nodes that no longer contain branching (ie. ifs and elses)"""

        groups = []
        allnodes = []

        if not isinstance(node, astroid.If):

            removelist = []
            iflist = []

            for blocktwo in node.nodes_of_class(astroid.If):
                removelist.append(blocktwo)
                iflist.append(blocktwo)

                for item in blocktwo.nodes_of_class(astroid.ALL_NODE_CLASSES):
                    if item not in removelist:
                        removelist.append(item)
            for block in node.nodes_of_class(astroid.ALL_NODE_CLASSES):
                if block not in removelist:
                    allnodes.append(block)



            groups.append(allnodes)

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




    def _check_group(self, node: Any, group: List) -> List:
        values = {}  # creates a 'notetaker' for when values are assigned and used.
        # the values of the keys in values will be a list where the first element is a number
        # 0 : assigned too but unused
        # -1 : used
        # >1 : assigned to before use.
        # and the second element the last assignment node,
        # which can be referenced as the unnecessary one if assigned to again before use.
        # the third element is whether it has been seen in the function before.

        for var in node.locals:  # initializes the values list with all the local variables.
            values[var] = [0, None, False]

        errors = []  # the list of problematic nodes
        errorexists = False  # initially we assume there is no error

        for block in node.nodes_of_class(astroid.ALL_NODE_CLASSES):
            # this will go through all the nodes in the function and analyze them, based on print nodes.
            if block in group:
                if not isinstance(block.parent, astroid.FunctionDef):
                    # the reason we care if the parent is the FunctionDef is because the only Name
                    # node that this will be the case for is the Name node for the .return field of the FunctionDef
                    # which isn't technically part of the function, it just describes the return type, not value.

                    if isinstance(block, astroid.AssignName):
                        # here we are checking if the node is one where assignment takes place.

                        if block.name in values and values[block.name][0] > -1 and not isinstance(block.parent,
                                                                                                  astroid.AugAssign) and \
                                values[block.name][2]:
                            # if it is already in the values list and being reassigned before use then there
                            # is unnecessary assignment and we should return True with the problematic node that
                            # assigned before this assignment because it is useless.
                            # KEY NOTE, this is unless it is part of an augmented assignment!
                            errors.append(values[block.name][1].parent)  # this will add the parent node
                            # so the whole line is highlighted
                            errorexists = True

                        elif block.name in values:
                            # Either the name isn't in values or it is
                            # in values and its value is -1 so it has been used.
                            # so we just reset to now unused with the new value. Either way the same thing is done.
                            values[block.name] = [0, block, True]

                    elif isinstance(block, astroid.Name) and block.name in values:
                        # here we check if the value is being used.
                        values[block.name] = [-1, None, True]

            for val in values:
                # this will check at the end if there were values unused.
                if values[val][0] > -1 and values[val][2]:
                    errors.append(values[val][1].parent)
                    errorexists = True

            return errors

    # pass in message symbol as a parameter of check_messages
    @check_messages("unnecessary-assignment")
    def visit_functiondef(self, node):
        """Visits nodes of functionDef type in file to check unnecessary assignment."""
        checks = self._check_unnecessary_assignment(node)
        if not checks == []:
            # this will return the problematic node.
            for item in checks:
                self.add_message('unnecessary-assignment', node=item)


def register(linter):
    """Registers linter."""
    linter.register_checker(UnnecessaryAssignmentChecker(linter))
