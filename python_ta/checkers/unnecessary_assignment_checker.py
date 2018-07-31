"""
Checker for unnecessary assignment to a variable.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from typing import Any
from typing import List


class PathLink:
    """
    A class representing one block of code without any branching due to if statements, and the blocks that follow it.
    """
    def __init__(self, value=None, nextelement=None)-> None:
        """
        Initializes the Link, with value None and an empty list for next.
        """
        self.value = value
        if nextelement is None:
            self.next = []

    def add_next(self, followinglink: Any) -> None:
        """
        Appends followinglink to self.next.
        """
        self.next.append(followinglink)

    def set_value(self, value: Any) -> None:
        """
        Sets self.value to value.
        """
        self.value = value

    def find_longest(self, sofar: int) -> int:
        """
        Find (recursively) the longest chain of Pathlinks starting from this one.
        """
        sofar += 1
        if self.next == []:
            return sofar
        else:
            return max([z.next.find_longest(sofar) for z in self.next])

    def find_stubs(self) -> Any:
        """
        Finds every path from self to None.
        """

        if self.next == []:
            return self
        else:
            return sum([x.find_stubs() for x in self.next], [])


class PathChain:
    """
    A class representing the different execution paths of a program.
    Composed of a PathLink pointing to the following Pathlink, or multiple
    if necessary due branching of the execution path that the PathChain represents.
    """
    def __init__(self)-> None:
        """
        Initializes the structure, with no PathLinks set as first or last, and length zero.
        """
        self.length = 0
        self.first = None
        # self.last = None   ??? Can we guarantee that different paths all have the same ends?

    def add(self, newlink: PathLink) -> None:
        """
        Adds newlink to the existing PathChain.
        """
        if self.first is None:
            self.first = newlink
            self.length = newlink.find_longest(0)
        else:
            self.length += 1


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

    def _check_unnecessary_assignment(self, node: Any)-> List[Any]:
        """Returns a list of nodes within the function that are instances of unnecessary assignment."""

        # This is the list of lists where each one is the nodes involved in a specific execution path the
        # computer can take through the function. This accounts for all branching execution paths due to ifs.
        groups = self._split_into_groups(node, [[]])
        examplepathchain = self._make_pathchain(node)
        # This initializes the list of nodes where unnecessary assignment has taken place.
        allerrors = []

        # This for loop iterates over execution path.
        for group in groups:

            # This errors variable will be a list of errors for given execution path
            errors = self._check_group(node, group)

            # The following loop will effectively add each of the errors for the current path to the total errors.
            for error in errors:
                if error not in allerrors:
                    allerrors.append(error)

        return allerrors

    def _make_pathchain(self, node: Any, branch=None)-> Any:
        """
        Returns a PathChain for the node given.
        """

        firstlink = PathLink([])
        link = firstlink

        if not isinstance(node, astroid.If):

            for item in node.nodes_of_class(astroid.ALL_NODE_CLASSES):

                if isinstance(item, astroid.If):

                    for test in item.test:
                        for testpart in test.nodes_of_class(astroid.ALL_NODE_CLASSES):
                            link.value.append(testpart)
                    link.next.append = self._make_pathchain(item, 'body')
                    link.next.append = self._make_pathchain(item, 'orelse')
                    newlink = PathLink([])
                    for nextstep in link.next:
                        should_rejoin = True
                        for stub in nextstep.find_stubs():
                            for stubelement in stub.value:
                                if isinstance(stubelement, astroid.Return):
                                    should_rejoin = False
                        if should_rejoin:
                            nextstep.next = newlink
                    link = newlink
                else:
                    for val in node.nodes_of_class(astroid.ALL_NODE_CLASSES):
                        link.value.append(val)

        elif isinstance(node, astroid.If) and branch == 'body':
            for item in node.body:

                if isinstance(item, astroid.If):

                    link.next.append = self._make_pathchain(item, 'body')
                    link.next.append = self._make_pathchain(item, 'orelse')
                    newlink = PathLink([])
                    for nextstep in link.next:
                        should_rejoin = True
                        for stub in nextstep.find_stubs():
                            for stubelement in stub.value:
                                if isinstance(stubelement, astroid.Return):
                                    should_rejoin = False
                        if should_rejoin:
                            nextstep.next = newlink
                    link = newlink
                else:
                    for val in node.nodes_of_class(astroid.ALL_NODE_CLASSES):
                        link.value.append(val)
            return firstlink

        elif isinstance(node, astroid.If) and branch == 'orelse':
            for item in node.orelse:

                if isinstance(item, astroid.If):

                    link.next.append = self._make_pathchain(item, 'body')
                    link.next.append = self._make_pathchain(item, 'orelse')
                    newlink = PathLink([])
                    for nextstep in link.next:
                        should_rejoin = True
                        for stub in nextstep.find_stubs():
                            for stubelement in stub.value:
                                if isinstance(stubelement, astroid.Return):
                                    should_rejoin = False
                        if should_rejoin:
                            nextstep.next = newlink
                    link = newlink
                else:
                    for val in node.nodes_of_class(astroid.ALL_NODE_CLASSES):
                        link.value.append(val)
            return firstlink

        returnvalue = PathChain
        returnvalue.first = firstlink
        return returnvalue





def _split_into_groups(self, node: Any, paths: List) -> List[List]:
    """
    Given a function node, recursively creates a list of lists;
    where each list is a series of nodes that would execute for a given path of execution
    the computer would take through the function. The returned list of lists is
    effectively a list of every possible path of execution.
    """

    if not isinstance(node, astroid.If):

        # allnodes will be every node in the function body.
        allnodes = []

        # This for loop will add every node in the .body field to the allnodes list.
        for item in node.body:

            # This inner for loop will add all the child nodes of the current node in the body to allnodes as well.
            for itemtwo in item.nodes_of_class(astroid.ALL_NODE_CLASSES):
                allnodes.append(itemtwo)

        # This while loop will dictate when every node has been evaluated and added to a path of execution.
        while not allnodes == []:

                # This if let us determine if branching has occurred at the current node we look at.
                if isinstance(allnodes[0], astroid.If):

                    # This will double the number of execution paths.
                    paths = self._clone(paths)

                    # This will add the different nodes for both executions to the now doubled paths.
                    paths = self._split_into_groups(allnodes[0], paths)

                    # This is a list of nodes that were involved in the branching and should not be
                    # considered further as they have been added to the separate paths already.
                    removelist = []

                    # Here we add all the children of the if node to the list of nodes to be removed from allnodes.
                    for item in allnodes[0].nodes_of_class(astroid.ALL_NODE_CLASSES):
                        removelist.append(item)

                    # This will remove the child nodes of the IF node from allnodes.
                    for itemtwo in removelist:
                        allnodes.pop(allnodes.index(itemtwo))

                else:

                    # This will add the node in question to every execution path.
                    for execution_path in paths:
                        execution_path.append(allnodes[0])

                    # This will remove the node in question from allnodes.
                    allnodes.pop(0)

    elif isinstance(node, astroid.If):

        # This will be the split index. Where half of the execution paths will before in the list and the
        # other half after. (based on the if and else)
        divergeindex = int(len(paths) / 2)

        # This will add the nodes involved for the test in the IF to every execution path.
        for execution in paths:
            for test in node.test.nodes_of_class(astroid.ALL_NODE_CLASSES):
                execution.append(test)

        # For every element in the body it should either be added to the execution path or
        # further branch the execution paths that can be taken.
        for element in node.body:

            # If the node in question is an IF node it should create another branch in execution paths.
            if isinstance(element, astroid.If):

                # This for loop will look at the body branch only.
                branch = []
                for x in range(divergeindex):
                    branch.append(paths[x])

                # This will clone that branch.
                branch = self._clone(branch)

                # This will go and fill in those execution paths.
                branch = self._split_into_groups(element, branch)

                # This will add those execution paths back into the paths list and adjust divergeindex.
                for item in branch:
                    if item not in paths:
                        paths.insert(divergeindex, item)
                        divergeindex += 1

            else:

                # This will add the element to the if paths.
                for child in element.nodes_of_class(astroid.ALL_NODE_CLASSES):
                    for i in range(len(paths)):
                        if i < divergeindex:
                            paths[i].append(child)

        for elementtwo in node.orelse:

            # If the node in question is an IF node it should create another branch in execution paths.
            if isinstance(elementtwo, astroid.If):

                # This for loop will look at only the orelse branch.
                branch = []
                for x in range(divergeindex, len(paths)):
                    branch.append(paths[x])

                # This will clone that branch.
                branch = self._clone(branch)

                # This will add those execution paths back into the paths list and adjust divergeindex.
                branch = self._split_into_groups(elementtwo, branch)
                for item in branch:
                    if item not in paths:
                        paths.append(item)
                        divergeindex += 1

            else:

                # This will add the element to the orelse paths.
                for child in elementtwo.nodes_of_class(astroid.ALL_NODE_CLASSES):
                    for i in range(len(paths)):
                        if not i < divergeindex:
                            paths[i].append(child)

    return paths

def _clone(self, groups: List) -> List:
    """
    This helper function will clone the existing groups. It will return the lists provided
    along with an identical copy of each.
    """

    # The new list to be filled with the originals and their clones.
    original_plus_clone = []

    # This will append the the original groups to the new version which will have clones.
    for y in groups:
        original_plus_clone.append(y)

    for x in groups:

        # This initializes a list which will built up to be a copy of x.
        clone = []

        # This for loop will add every element in x to clone.
        for item in x:
            clone.append(item)

        # This will append clone to original_plus_clone after x.
        original_plus_clone.append(clone)

    return original_plus_clone

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

        if block in group and not isinstance(block.parent, astroid.FunctionDef):

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

    for val in values:
        # This will check at the end if there were any unused values.
        if isinstance(values[val], astroid.AssignName):
            errors.append(values[val].parent)

    return errors

# pass in message symbol as a parameter of check_messages
@check_messages("unnecessary-assignment")
def visit_functiondef(self, node: Any):
    """Visits nodes of functionDef type in file to check unnecessary assignment."""

    checks = self._check_unnecessary_assignment(node)

    if not checks == []:
        # This for loop will add an error message for each instance of unnecessary assignment.
        for item in checks:
            self.add_message('unnecessary-assignment', node=item)


def register(linter):
    """Registers linter."""
    linter.register_checker(UnnecessaryAssignmentChecker(linter))

