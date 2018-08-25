"""
Checker for unnecessary assignment to a variable.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from typing import Any
from typing import List


class ExecutionBlock:
    """
    A class representing one block of code without any branching/looping, and the blocks that follow it.
    """
    def __init__(self, value: List[astroid.node_classes.NodeNG] = None, nextelement: List[astroid.node_classes.NodeNG]
                 = None)-> None:
        """
        Initializes the ExecutionBlock, with an empty list for the .nodes and .next attributes as default.
        """
        if value is None:
            self.nodes = []
        if nextelement is None:
            self.next = []

    def find_stubs(self, visited: List) -> List:
        """
        Finds every path from self to None recursively.
        """
        newvisited = visited  # A list of executionblocks visited.
        newvisited.append(self)  # To append the current EB that is looked at to the visited.

        if self.next == []:
            return [self]  # If the current EB being looked at has an empty .next then it is a stub.
        else:

            lst = []
            for x in self.next:
                if x not in visited:  # All the remaining ExecutionBlocks to go look for stubs at.
                    lst.append(x)

            to_be_returned = sum([x.find_stubs([newvisited]) for x in lst], [])  # Return a flattened list of stubs.

            lst2 = []
            for item in to_be_returned:
                if item not in lst2:  # Guarantees no stub duplicates, such as from if and else branches rejoining.
                    lst2.append(item)

            return lst2


class UnnecessaryAssignmentChecker(BaseChecker):
    """Checker for unnecessary assignment to variables in several cases."""
    __implements__ = IAstroidChecker

    name = 'unnecessary-assignment'
    msgs = {'E9917': ('This variable assignment is unnecessary.', 'unnecessary-assignment',
                      'Used when there is an assignment statement that could be '
                      'removed without changing the meaning of the program.')
            }

    # this is important so that the checker is executed in order. It seems all
    # the checkers have the same priority though.
    priority = -1

    def _check_unnecessary_assignment(self, node: astroid.FunctionDef)-> List[astroid.node_classes.NodeNG]:
        """Returns a list of nodes within the function that are instances of unnecessary assignment."""

        # Creates the graph structure representing the execution paths.
        examplepathchain = self._make_executionchain(node.body)

        # Finds all the unnecessary assignments in the function using breadth-first traversal.
        allerrors = self._checkchain(node, examplepathchain)

        return allerrors

    def _checkchain(self, node: astroid.FunctionDef, chainstart: ExecutionBlock)-> List:
        """Returns a list of nodes where unnecessary assignment has taken place. Using breadth first traversal of
        the execution graph provided as a parameter."""

        visited = set(())  # The execution blocks already visited.
        errors = []  # The accumulator for the nodes which are instances of unnecessary assignment.
        blocks = [chainstart]  # 'blocks' is the queue used for the BF traversal, starting at the first execution block.

        while blocks != []:  # The body of code for traversal.

            next_block = blocks.pop(0)  # Pops the first execution block in the queue to 'scan' for errors.

            visited.add(id(next_block))  # Adds the current execution block being looked at to the visited set.

            thisblockerror = self._check_group(node, next_block)  # Using a helper function, checks
            # the current execution block for instances of unnecessary assignment.

            for er in thisblockerror:  # Adds the errors in this executionblock to the overall list.
                if er not in errors:
                    errors.append(er)

            for follow_up in next_block.next:  # Adds the execution blocks following the current one to the queue.
                if id(follow_up) not in visited:
                    blocks.append(follow_up)

        return errors

    def _make_executionchain(self, lst: List[astroid.node_classes.NodeNG])-> Any:
        """
        Returns an ExecutionBlock for the list of nodes given.
        """

        firstlink = ExecutionBlock()  # an empty ExecutionBlock to begin with.
        link = firstlink  # Creates a 'link' variable that points to the current ExecutionBlock being built.

        for item in lst:  # This for loop will traverse the list of nodes and determine whether to add them
                # to the current execution block or create more depending on if the node is a For, While, If, Return, or
                # other type of node.

            if isinstance(item, astroid.If):
                # If the node is an If node, then the execution graph should branch into two.

                link.nodes.append(item.test)  # The test attribute will be executed before branching occurs, and
                # so should be added to the current executionblock.

                link.next.append(self._make_executionchain(item.body))  # Creates new EB for the if part.
                link.next.append(self._make_executionchain(item.orelse))  # Creates a new EB for the else part.

                newlink = ExecutionBlock()  # Creates a new link that will be the link to follow after the branches.

                for stub in link.find_stubs([]):  # This will find all the ends of the two new EB's.

                    should_rejoin = True  # The default is that the stubs should point to the newlink.

                    for stubelement in stub.nodes:

                        if isinstance(stubelement, astroid.Return):
                            should_rejoin = False  # If there is a Return node in the stub, then it
                            # should remain as a leaf of the execution graph.

                    if should_rejoin:
                        stub.next.append(newlink)  # If the EB is not a leaf, it now points to the newlink.

                link = newlink  # Now the link will be the newlink so nodes in the list will be added
                # after the branching.

            elif isinstance(item, astroid.For):

                link.nodes.append(item.target)  # The .target and .iter fields should be added to the current EB.
                link.nodes.append(item.iter)

                link.next.append(self._make_executionchain(item.body))  # Creates an executionblock for the FOR body.

                newlink = ExecutionBlock()  # Creates a new link that will be the link to follow after the loop.

                for stub in link.find_stubs([]):  # This will find and iterate through the stubs
                    # of the execution block of the for loop body.

                    should_rejoin = True  # By default they should rejoin with the EB following the FOR loop.

                    for stubelement in stub.nodes:
                        if isinstance(stubelement, astroid.Return):
                            should_rejoin = False  # If there is a Return node in it, the stub should not rejoin.

                    if should_rejoin:
                        # Because this is a looping body of code, the stubs should point to the next node
                        # as well as the beginning of the loop.
                        stub.next.append(link.next[0])
                        stub.next.append(newlink)

                link = newlink  # Now the link will be the newlink so nodes in the list will be added
                # after the loop.

            elif isinstance(item, astroid.While):

                link.nodes.append(item.test)    # The .test field should be added to the current EB.

                link.next.append(self._make_executionchain(item.body))  # Makes the body of the while loop its own EB.

                newlink = ExecutionBlock()  # Creates a new link that will be the link to follow after the loop.

                for stub in link.find_stubs([]):  # This will find and iterate through the stubs
                    # of the execution block of the for loop body.

                    should_rejoin = True  # By default they should rejoin with the EB following the WHILE loop.

                    for stubelement in stub.nodes:

                        if isinstance(stubelement, astroid.Return):
                            should_rejoin = False  # If there is a Return node in it, the stub should not rejoin.

                    if should_rejoin:
                        # Because this is a looping body of code, the stubs should point to the next node
                        # as well as the beginning of the loop.
                        stub.next.append(link.next[0])
                        stub.next.append(newlink)

                link = newlink  # Now the link will be the newlink so nodes in the list will be added
                # after the loop.

            elif isinstance(item, astroid.Return):

                for itemtwo in item.nodes_of_class(astroid.ALL_NODE_CLASSES):
                    link.nodes.append(itemtwo)

                # If the node in question is a Return node, an immedate end to the execution block should be triggered.
                return firstlink

            else:
                for itemtwo in item.nodes_of_class(astroid.ALL_NODE_CLASSES):
                    link.nodes.append(itemtwo)  # In the general case, the node and its children will be added to
                    # the current ExecutionBlock.

        return firstlink

    def _check_group(self, node: astroid.FunctionDef, chunk: ExecutionBlock) -> List[Any]:
        """
        This function will check the given group of nodes in the ExecutionBlock (chunk) within the context
        of the function node to check for unnecessary assignment. It will return the nodes that are unnecessary.
        """

        values = {}  # creates a 'notetaker' for when values are assigned and used.
        leftoversgroup = []  # A list of nodes that were assigned to but unused by the end of ExecutionBlock.nodes

        for var in node.locals:  # initializes the values list with all the local variables.
            values[var] = None

        errors = []  # the list of problematic nodes

        for block in chunk.nodes:  # This for loop should iterate through all the nodes in the ExecutionBlock (.nodes).

            if isinstance(block, astroid.AssignName):
                # here we are checking if the given node is one where assignment takes place.

                if block.name in values and values[block.name] is not None and \
                        not isinstance(block.parent, astroid.AugAssign) and \
                        isinstance(values[block.name], astroid.AssignName):
                    # if it is already in the values list and being reassigned before use then there
                    # is unnecessary assignment and we should add the previous node to errors.
                    # KEY NOTE: this is unless it is part of an augmented assignment, in which case we need
                    # previous assignment!

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

        for val in values:
            # This will check at the end if there were any unused values.
            if isinstance(values[val], astroid.AssignName):
                if isinstance(values[val].parent, astroid.For):
                    errors.append(values[val])  # The case when an indexing variable is unnecessary.
                else:
                    leftoversgroup.append(values[val])  # This will populate the leftoversgroup.

        for lo in leftoversgroup:  # This forloop will determine if there is any path through later executionblocks
            # that uses the given leftover assignment for each one in leftoversgroup. It is a breadth first search.

            visited = set(())  # The visited execution blocks.

            blocks = []  # This will set up the queue for execution blocks to check in breadth first traversal.
            for item in chunk.next:
                blocks.append(item)

            used = False  # The default assumption is that the leftover assignment is unnecessary.

            while blocks != []:  # This loop will keep track of the queue of EBs to visit for use.

                next_block = blocks.pop(0)  # Set the next_block to be looked at.

                visited.add(id(next_block))  # Adds the block being looked at to visited.

                seen = False  # The 'seen' variable allows the program to check if there has been an instance of the
                # variable in question, whether by reassignment or use.

                for part in next_block.nodes:  # Iterates over the nodes in the given execution block.

                    if seen is False and isinstance(part, astroid.Name) and part.name == lo.name:
                        # This occurs if the variable of the leftover assignment has been used.
                        used = True
                        seen = True

                    elif isinstance(part, astroid.AssignName):
                        if part.name == lo.name:

                            if isinstance(part.parent, astroid.AugAssign) and seen is False:
                                used = True  # If there is an AugAssign later it is a use.

                            seen = True  # If an AssignName of the same variable comes up then it does not matter
                            # if it is used later in this execution path.
                if used:
                    break  # If there is an instance of use the program should stop looking for this variable.

                for follow_up in next_block.next:

                    if id(follow_up) not in visited and seen is False:
                        blocks.append(follow_up)  # Adds the next execution block to the queue, if the variable has
                        # not been seen or used.

            if used is not True:
                errors.append(lo)  # If the assignment remains unnecessary in all execution paths then it is an error.

        return errors

    @check_messages("unnecessary-assignment")
    def visit_functiondef(self, node: Any):
        """Visits nodes of FunctionDef type in the module to check unnecessary assignment."""

        checks = self._check_unnecessary_assignment(node)

        if not checks == []:

            # This for loop will add an error message for each instance of unnecessary assignment.
            for item in checks:
                self.add_message('unnecessary-assignment', node=item)


def register(linter):
    """Registers linter."""
    linter.register_checker(UnnecessaryAssignmentChecker(linter))
