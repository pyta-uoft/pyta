"""Checker for redundant assignment statements in the program.

An assignment statement is redundant if it satisfies the following two properties:

    1. Every path from a definition of a variable `v` to its first usage
    goes through at least one re-definition of `v`.

    2. Removing the statement from the program does not in any way change
    the behavior of the program.
"""
from typing import List, Set, Union

from astroid import nodes
from pylint.checkers import BaseChecker, utils
from pylint.checkers.utils import check_messages
from pylint.interfaces import IAstroidChecker

from python_ta.cfg.graph import CFGBlock, ControlFlowGraph


class RedundantAssignmentChecker(BaseChecker):

    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = "redundant_assignment"
    # use dashes for connecting words in message symbol
    msgs = {
        "E9959": (
            "This assignment statement is redundant;" " You can remove it from the program.",
            "redundant-assignment",
            "This assignment statement is redundant;" " You can remove it from the program.",
        )
    }

    # this is important so that your checker is executed before others
    priority = -1

    def __init__(self, linter=None):
        super().__init__(linter=linter)
        self._redundant_assignment: Set[nodes.Assign] = set()

    @check_messages("redundant-assignment")
    def visit_assign(self, node: nodes.Assign):
        if node in self._redundant_assignment:
            self.add_message("redundant-assignment", node=node)

    @check_messages("redundant-assignment")
    def visit_augassign(self, node: nodes.AugAssign):
        if node in self._redundant_assignment:
            self.add_message("redundant-assignment", node=node)

    def visit_module(self, node: nodes.Module):
        self._analyze(node)

    def visit_functiondef(self, node: nodes.FunctionDef):
        self._analyze(node)

    def _analyze(self, node: Union[nodes.Module, nodes.FunctionDef]) -> None:
        """Runs the backward data flow algorithm on a `Module` or `Function` CFG, which in turn
        appends `Assign` nodes to `self.redundant_assignment` if it is redundant.

        Data flow algorithms retrieved from:
        https://www.seas.harvard.edu/courses/cs252/2011sp/slides/Lec02-Dataflow.pdf#page=31
        """
        # Stores all the variable names that will be re-defined before any usage at a
        # particular program point.
        out_facts = {}
        cfg = ControlFlowGraph()
        cfg.start = node.cfg_block
        worklist = list(cfg.get_blocks_postorder())
        worklist.reverse()

        all_assigns = self._get_assigns(node)
        for block in worklist:
            out_facts[block] = all_assigns.copy()

        while len(worklist) != 0:
            b = worklist.pop()
            outs = [out_facts[p.target] for p in b.successors if p.target in out_facts]
            if outs == []:
                in_facts = set()
            else:
                in_facts = set.intersection(*outs)
            temp = self._transfer(b, in_facts)
            if temp != out_facts[b]:
                out_facts[b] = temp
                worklist.extend([pred.source for pred in b.predecessors if pred.source.reachable])

    def _transfer(self, block: CFGBlock, out_facts: Set[str]) -> Set[str]:
        gen = out_facts.copy()
        kill = set()
        for statement in reversed(block.statements):
            if isinstance(statement, nodes.FunctionDef):
                # `nodes_of_class` below doesnt block looking for required nodes
                # in function definitions, hence this case.
                continue
            for node in statement.nodes_of_class(
                (
                    nodes.AssignName,
                    nodes.DelName,
                    nodes.Name,
                    nodes.Nonlocal,
                    nodes.Global,
                ),
                nodes.FunctionDef,
            ):
                if isinstance(node, nodes.AssignName):
                    if node.name in gen.difference(kill):
                        self._redundant_assignment.add(node.parent)
                    elif node.parent in self._redundant_assignment:
                        self._redundant_assignment.remove(node.parent)

                    # When node.parent is an AugAssign, the name counts as a use of the variable,
                    # and so is added to kill.
                    if isinstance(node.parent, nodes.AugAssign):
                        kill.add(node.name)
                    else:
                        kill.discard(node.name)
                    gen.add(node.name)
                elif isinstance(node, (nodes.Nonlocal, nodes.Global)):
                    kill.difference_update(set(node.names))
                else:
                    kill.add(node.name)

        return gen.difference(kill)

    def _get_assigns(self, node: Union[nodes.FunctionDef, nodes.Module]) -> Set[str]:
        """Returns a set of all local and parameter variables that could be
        defined in the program (either a function or module).

        IF a variable 'v' is defined in a function and there is no global/nonlocal
        statement applied to 'v' THEN 'v' is a local variable.

        Note that `local variable` in the context of a module level analysis,
        refers to global variables.
        """
        assigns = set()
        kills = set()
        for name, assign_nodes in node.locals.items():
            if any(isinstance(elem, nodes.AssignName) for elem in assign_nodes):
                assigns.add(name)
        return assigns.difference(kills)


def register(linter):
    linter.register_checker(RedundantAssignmentChecker(linter))
