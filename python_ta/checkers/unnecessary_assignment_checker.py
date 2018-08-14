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
    name = 'unnecessary-assignment'
    msgs = {'E9917': ('This variable assignment is unnecessary.', 'unnecessary-assignment',
                      'Used when there is an assignment statement that could be '
                      'removed without changing the meaning of the program.')
            }

    # this is important so that your checker is executed before others. It seems all
    # the checkers have the same priority though.
    priority = -1

    def _check_unnecessary_assignment(self, node: astroid.FunctionDef)-> List[Any]:
        """Returns a list of nodes within the function that are instances of unnecessary assignment."""

        lst = []
        for item in node.body:
            lst.append(item)

        examplepathchain = self._make_executionchain(lst)

        allerrors = self._checkchain(node, examplepathchain)

        return allerrors

    def _checkchain(self, node: astroid.FunctionDef, chainstart: Any)-> List:
        visited = set(())
        errors = []
        blocks = [chainstart]
        leftovers = []
        while blocks != []:
            next_block = blocks.pop(0)
            visited.add(id(next_block))
            thisblockerror = self._check_group(node, next_block, leftovers)
            for er in thisblockerror[0]:
                if er not in errors:
                    errors.append(er)

            leftovers = thisblockerror[1]

            for follow_up in next_block.next:
                if id(follow_up) not in visited:
                    blocks.append(follow_up)

        return errors

    def _make_executionchain(self, lst: List[astroid.node_classes.NodeNG])-> Any:
        """
        Returns a PathChain for the node given.
        """

        firstlink = ExecutionBlock()
        link = firstlink

        for item in lst:

            if isinstance(item, astroid.If):

                link.nodes.append(item.test)

                lst1 = []
                lst2 = []

                for bod in item.body:
                    lst1.append(bod)
                for orls in item.orelse:
                    lst2.append(orls)

                link.next.append(self._make_executionchain(lst1))
                link.next.append(self._make_executionchain(lst2))

                newlink = ExecutionBlock()

                for nextstep in link.next:
                    for stub in nextstep.find_stubs([]):

                        should_rejoin = True
                        for stubelement in stub.nodes:
                            if isinstance(stubelement, astroid.Return):
                                should_rejoin = False
                        if should_rejoin:
                            nextstep.next.append(newlink)

                link = newlink

            elif isinstance(item, astroid.For):
                link.nodes.append(item.target)
                link.nodes.append(item.iter)
                lst3 = []

                for objects in item.body:
                    lst3.append(objects)

                link.next.append(self._make_executionchain(lst3))
                newlink = ExecutionBlock()

                for nextstep in link.next:
                    for stub in nextstep.find_stubs([]):

                        should_rejoin = True
                        for stubelement in stub.nodes:
                            if isinstance(stubelement, astroid.Return):
                                should_rejoin = False
                        if should_rejoin:
                            nextstep.next.append(nextstep)
                            nextstep.next.append(newlink)

                link = newlink

            elif isinstance(item, astroid.While):
                link.nodes.append(item.test)
                lst4 = []

                for objects in item.body:
                    lst4.append(objects)

                link.next.append(self._make_executionchain(lst4))
                newlink = ExecutionBlock()

                for nextstep in link.next:
                    for stub in nextstep.find_stubs([]):

                        should_rejoin = True
                        for stubelement in stub.nodes:
                            if isinstance(stubelement, astroid.Return):
                                should_rejoin = False
                        if should_rejoin:
                            nextstep.next.append(nextstep)
                            nextstep.next.append(newlink)

                link = newlink

            else:
                for itemtwo in item.nodes_of_class(astroid.ALL_NODE_CLASSES):
                    link.nodes.append(itemtwo)

        return firstlink

    def _check_group(self, node: astroid.FunctionDef, chunk: Any, leftovers: list) -> List[Any]:
        """
        This function will check the given group of nodes within the context
        of the function node to check for unnecessary assignment.
        """

        values = {}  # creates a 'notetaker' for when values are assigned and used.
        leftoversgroup = []
        for var in node.locals:  # initializes the values list with all the local variables.
            values[var] = None

        errors = []  # the list of problematic nodes

        for block in chunk.nodes:

            if isinstance(block, astroid.AssignName):
                # here we are checking if the given node is one where assignment takes place.

                if block.name in values and values[block.name] is not None and \
                        not isinstance(block.parent, astroid.AugAssign) and \
                        isinstance(values[block.name], astroid.AssignName):

                    # if it is already in the values list and being reassigned before use then there
                    # is unnecessary assignment and we should add the previous node to errors.
                    # KEY NOTE, this is unless it is part of an augmented assignment!
                    errors.append(values[block.name].parent)  # this will add the parent node
                    # so the whole line is highlighted

                    # Replace the current node being "remembered" as the last instance of the variable.
                    values[block.name] = block

                elif block.name in values:

                    # Either it hasn't been assigned to yet or it has been used.
                    # In this case it is not an error and we should simply replace the current
                    # node being "remembered" as the last instance of the variable.
                    values[block.name] = block

            elif isinstance(block, astroid.Name) and block.name in values:
                # Here we check if the value is being used.
                values[block.name] = block

                for lo in leftovers:
                    if lo.name == block.name:
                        leftovers.pop(leftovers.index(lo))

        for val in values:
            # This will check at the end if there were any unused values.
            if isinstance(values[val], astroid.AssignName):
                if isinstance(values[val].parent, astroid.For):
                    errors.append(values[val])
                else:
                    leftoversgroup.append(values[val])

        checked = []
        for lo in leftovers:
            leftoversgroup.append(lo)
        checked.append(errors)
        checked.append(leftoversgroup)
        return checked

        # pass in message symbol as a parameter of check_messages

    @check_messages("unnecessary-assignment")
    def visit_functiondef(self, node: Any):
        """Visits nodes of functionDef type in file to check unnecessary assignment."""

        checks = self._check_unnecessary_assignment(node)

        if not checks == []:
            # This for loop will add an error message for each instance of unnecessary assignment.
            for item in checks:
                self.add_message('unnecessary-assignment', node=item)


class ExecutionBlock:
    """
    A class representing one block of code without any branching due to if statements, and the blocks that follow it.
    """
    def __init__(self, value: List[astroid.node_classes.NodeNG] = None, nextelement: List[astroid.node_classes.NodeNG]
                 = None)-> None:
        """
        Initializes the Link, with value None and an empty list for next.
        """
        if value is None:
            self.nodes = []
        if nextelement is None:
            self.next = []

    def find_longest(self, sofar: int) -> int:
        """
        Find (recursively) the longest chain of ExecutionBlocks starting from this one.
        """
        sofar += 1
        if self.next == []:
            return sofar
        else:
            return max([z.next.find_longest(sofar) for z in self.next])

    def find_stubs(self, visited: List) -> Any:
        """
        Finds every path from self to None.
        """
        newvisited = visited
        newvisited.append(self)
        if self.next == []:
            return [self]
        else:
            lst = []
            for x in self.next:
                if x not in visited:
                    lst.append(x)
            return sum([x.find_stubs([newvisited]) for x in lst], [])


def register(linter):
    """Registers linter."""
    linter.register_checker(UnnecessaryAssignmentChecker(linter))
