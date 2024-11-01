"""Checker for redundant assignment statements in the program.

An assignment statement is redundant if it satisfies the following two properties:

    1. Every path from a definition of a variable `v` to its first usage
    goes through at least one re-definition of `v`.

    2. Removing the statement from the program does not in any way change
    the behavior of the program.
"""

from __future__ import annotations

from typing import Union

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter

from python_ta.cfg.graph import CFGBlock, ControlFlowGraph


class RedundantAssignmentChecker(BaseChecker):
    """A checker class for redundant assignment statements in the program.
    An assignment statement is redundant if it satisfies the following two properties:

    1. Every path from a definition of a variable `v` to its first usage
    goes through at least one re-definition of `v`.

    2. Removing the statement from the program does not in any way change
    the behavior of the program."""

    name = "redundant_assignment"
    msgs = {
        "E9959": (
            "Assigning to variable(s) %s here is redundant, because they are not used before getting reassigned later."
            " You can remove the assignment(s) without changing the behaviour of this code.",
            "redundant-assignment",
            "Assigning to variable(s) is redundant, because they are not used before getting reassigned later."
            " You can remove the assignment(s) without changing the behaviour of this code.",
        )
    }
    options = (
        (
            "z3",
            {
                "default": False,
                "type": "yn",
                "metavar": "<y or n>",
                "help": "Use Z3 to restrict control flow checks to paths that are logically feasible.",
            },
        ),
    )

    def __init__(self, linter=None) -> None:
        super().__init__(linter=linter)
        self._redundant_assignment: dict[
            nodes.Assign | nodes.AugAssign | nodes.AnnAssign, list[str]
        ] = {}

    @only_required_for_messages("redundant-assignment")
    def visit_assign(self, node: nodes.Assign) -> None:
        """Visit the assign node"""
        if node in self._redundant_assignment:
            self.add_message(
                "redundant-assignment", node=node, args=", ".join(self._redundant_assignment[node])
            )

    @only_required_for_messages("redundant-assignment")
    def visit_augassign(self, node: nodes.AugAssign) -> None:
        """ "Visit the augmented assign node"""
        if node in self._redundant_assignment:
            self.add_message("redundant-assignment", node=node, args=node.target.name)

    @only_required_for_messages("redundant-assignment")
    def visit_annassign(self, node: nodes.AnnAssign) -> None:
        """Visit the annotated assign node"""
        if node in self._redundant_assignment:
            self.add_message("redundant-assignment", node=node, args=node.target.name)

    def visit_module(self, node: nodes.Module) -> None:
        """Visit the module"""
        self._analyze(node)

    def visit_functiondef(self, node: nodes.FunctionDef) -> None:
        """Visit the function definition"""
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
        worklist = list(cfg.get_blocks_postorder(only_feasible=self.linter.config.z3))
        worklist.reverse()

        all_assigns = self._get_assigns(node)
        for block in worklist:
            out_facts[block] = all_assigns.copy()

        while len(worklist) != 0:
            b = worklist.pop()
            outs = [
                out_facts[p.target]
                for p in b.successors
                if p.target in out_facts and (not self.linter.config.z3 or p.is_feasible)
            ]
            if outs == []:
                in_facts = set()
            else:
                in_facts = set.intersection(*outs)
            temp = self._transfer(b, in_facts)
            if b in out_facts and temp != out_facts[b]:
                out_facts[b] = temp
                worklist.extend(
                    [
                        pred.source
                        for pred in b.predecessors
                        if pred.source.reachable and (not self.linter.config.z3 or pred.is_feasible)
                    ]
                )

    def _transfer(self, block: CFGBlock, out_facts: set[str]) -> set[str]:
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
                    # checking for parent node that accounts for parallel assignment
                    parent = (
                        node.parent.parent if isinstance(node.parent, nodes.Tuple) else node.parent
                    )
                    if node.name in gen.difference(kill):
                        # add redundant assignment
                        if parent not in self._redundant_assignment:
                            self._redundant_assignment[parent] = []
                        if node.name not in self._redundant_assignment[parent]:
                            self._redundant_assignment[parent].append(node.name)
                    elif (
                        parent in self._redundant_assignment
                        and node.name in self._redundant_assignment[parent]
                    ):
                        # remove redundant assignment
                        self._redundant_assignment[parent].remove(node.name)
                        if len(self._redundant_assignment[parent]) == 0:
                            self._redundant_assignment.pop(parent)

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

    def _get_assigns(self, node: Union[nodes.FunctionDef, nodes.Module]) -> set[str]:
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


def register(linter: PyLinter) -> None:
    """Required method to auto-register this checker to the linter"""
    linter.register_checker(RedundantAssignmentChecker(linter))
