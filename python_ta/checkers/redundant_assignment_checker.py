"""checker for variables that might not be defined in the program.
"""
from typing import Union
import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker, utils
from pylint.checkers.utils import check_messages
from python_ta.cfg.graph import CFGBlock, ControlFlowGraph
from typing import Set


class RedundantAssignmentChecker(BaseChecker):

    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'redundant_assignment'
    # use dashes for connecting words in message symbol
    msgs = {'E9969': ('Description',
                      'redundant-assignment',
                      'Description'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    def __init__(self, linter=None):
        super().__init__(linter=linter)
        self._redundant_assignment: Set[astroid.Assign] = set()

    @check_messages('redundant-assignment')
    def visit_assign(self, node):
        """Adds message if there exists a path from the start block to node where
        a variable used by node might not be defined."""
        if node in self._redundant_assignment:
            self.add_message('redundant-assignment', node=node)

    def visit_module(self, node):
        self._analyze(node)

    def visit_functiondef(self, node):
        self._analyze(node)

    def _analyze(self, node: Union[astroid.Module, astroid.FunctionDef]) -> None:
        """Runs the backward data flow algorithm on a `Module` or `Function` CFG, which in turn
        appends `Assign` nodes to `self.redundant_assignment` if it is redundant.

        Data flow algorithms retrieved from:
        https://www.seas.harvard.edu/courses/cs252/2011sp/slides/Lec02-Dataflow.pdf#page=31
        """
        in_facts = {}
        cfg = ControlFlowGraph()
        cfg.start = node.cfg_block
        blocks = list(cfg.get_blocks())
        blocks.reverse()

        all_assigns = self._get_assigns(node)
        for block in blocks:
            # out_facts[block] = all_assigns.copy()
            in_facts[block] = {}

        worklist = blocks
        while len(worklist) != 0:
            b = worklist.pop()
            ins = [in_facts[p.target] for p in b.successors if p.target in in_facts]
            if ins == []:
                out_facts = set()
            else:
                out_facts = set.intersection(*ins)
            temp = self._transfer(b, out_facts, all_assigns)
            if temp != in_facts[b]:
                in_facts[b] = temp
                worklist.extend([pred.source for pred in b.predecssors])

    def _transfer(self, block: CFGBlock, out_facts: Set[str]) -> Set[str]:
        gen = out_facts.copy()
        kill = set()
        for statement in reversed(block.statements):
            if isinstance(statement, astroid.FunctionDef):
                continue
            for node in statement.nodes_of_class((astroid.AssignName, astroid.DelName, astroid.Name),
                                              astroid.FunctionDef):
                if isinstance(node, astroid.AssignName):
                    if node.name in gen.difference(kill):
                        self._redundant_assignment.add(node.parent)
                        continue
                    gen.add(node.name)
                else:
                    kill.add(node.name)
        return gen.difference(kill)

    def _get_assigns(self, node: Union[astroid.FunctionDef, astroid.Module]) -> Set[str]:
        """Returns a set of all local and parameter variables that could be
        defined in the program (either a function or module).

        IF a variable 'v' is defined in a function and there is no global/nonlocal
        statement applied to 'v' THEN 'v' is a local variable.

        Note that `local variable` in the context of a module level analysis,
        refers to global variables.
        """
        assigns = set()
        kills = set()
        for name, nodes in node.scope().locals.items():
            if any(isinstance(elem, astroid.AssignName) for elem in nodes):
                assigns.add(name)
        for statement in node.nodes_of_class((astroid.Nonlocal, astroid.Global), astroid.FunctionDef):
            for name in statement.names:
                kills.add(name)

        return assigns.difference(kills)


def register(linter):
    linter.register_checker(RedundantAssignmentChecker(linter))
