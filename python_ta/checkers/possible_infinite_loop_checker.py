"""checker for a while loop that does not mutate any condition variable in its body.
"""
import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from typing import Set, Generator, Dict
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
        if not self._check_loop_variable_mutation(node):
            self.add_message('possible-infinite-loop', node=node)

    def _check_loop_variable_mutation(self, node: astroid.While) -> bool:
        """Returns True if the variable used in the loop condition is mutated in
        any path of the loop body.
        """
        test_block = node.cfg_block
        # True iff the inf_type is an immutable type.
        names: Dict[str, bool] = {}
        for node in node.test.nodes_of_class(astroid.Name, (astroid.Call, astroid.Attribute)):
            names[node.name] = type(node.inf_type).__name__ in \
                               ('str', 'int', 'float', 'bool', 'tuple', 'frozenset')

        after_loop_block = test_block.successors[1].target

        if len(names) < 1:
            return True

        return self._visit_blocks(test_block, after_loop_block, names)

    def _visit_blocks(self, start_block: CFGBlock, end_block: CFGBlock, names: Dict[str, bool]) -> bool:
        """Visits every reachable block that succeeds `start_block` and preceeds `end_block`
        and Returns True if at least one `AssignName` node is found that matches the
        elements in `names`.

        Precondition:
            - `start_block` is the test block of the while loop.
            - `end_block` is the after while block.
        """
        then_block = start_block.successors[0].target
        for block in self._get_blocks(then_block, visited={end_block.id, start_block.id}):
            for statement in block.statements:
                for node in statement.nodes_of_class((astroid.AssignName, astroid.Name)):
                    if node.name in names:
                        if isinstance(node, astroid.AssignName) and not names[node.name] \
                                or isinstance(node, astroid.Name) and names[node.name]:
                            return True
        return False

    def _get_blocks(self, block: CFGBlock, visited: Set[int]) -> Generator[CFGBlock, None, None]:
        if block.id in visited:
            return

        yield block
        visited.add(block.id)

        for edge in block.successors:
            yield from self._get_blocks(edge.target, visited)


def register(linter):
    linter.register_checker(PossibleInfiniteLoopChecker(linter))
