"""checker for a loop that can only ever run for one iteration.
"""
import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from typing import Set, Generator
from python_ta.cfg import CFGBlock


class PossibleInfiniteLoopChecker(BaseChecker):

    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'possible_infinite_loop'
    # use dashes for connecting words in message symbol
    msgs = {'E9976': ('This loop might not terminate.',
                      'possible-infinite-loop',
                      'Reported when the variable/s used in the while loop condition'
                      'is not mutated in any path of the code.'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    # pass in message symbol as a parameter of check_messages
    @check_messages('possible-infinite-loop')
    def visit_while(self, node):
        if self._check_loop_variable_mutation(node):
            self.add_message('possible-infinite-loop', node=node)

    def _check_loop_variable_mutation(self, node: astroid.While) -> bool:
        """Returns whether the variable used in the loop condition is mutated in
        any path of the loop body.
        """
        test_block = node.cfg_block
        names: Set[str] = set()
        for node in node.test.nodes_of_class(astroid.Name, (astroid.Call, astroid.Attribute)):
            names.add(node.name)

        then_block = test_block.successors[0].target
        after_loop_block = test_block.successors[1].target
        self._visit_blocks(then_block, after_loop_block, names)

        return bool(len(names))

    def _visit_blocks(self, start_block: CFGBlock, end_block: CFGBlock, names: Set[str]) -> None:
        """Visits every reachable block that succeeds `start_block` and preceeds `end_block`
        and if any `AssignName` nodes are found that matches the elements in `names`,
        it is removed from the set.

        Precondition:
            - `start_block` is the test block of the while loop.
            - `end_block` is the after while block.
        """
        for block in self._get_blocks(start_block, visited={end_block.id}):
            if len(names) == 0:
                return None
            for statement in block.statements:
                for node in statement.nodes_of_class(astroid.AssignName):
                    if node.name in names:
                        names.remove(node.name)
                for node in statement.nodes_of_class(astroid.Name):
                    if node.name in names:
                        names.remove(node.name)
        return None

    def _get_blocks(self, block: CFGBlock, visited: Set[int]) -> Generator[CFGBlock, None, None]:
        if block.id in visited:
            return

        yield block
        visited.add(block.id)

        for edge in block.successors:
            yield from self._get_blocks(edge.target, visited)


def register(linter):
    linter.register_checker(PossibleInfiniteLoopChecker(linter))
