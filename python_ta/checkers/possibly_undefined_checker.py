"""checker for a loop that can only ever run for one iteration.
"""
from typing import Union
import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from python_ta.cfg.graph import CFGBlock
from astroid.node_classes import NodeNG
from typing import Set, Dict, Tuple, List


class PossiblyUndefinedChecker(BaseChecker):

    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'possibly_undefined'
    # use dashes for connecting words in message symbol
    msgs = {'E9969': ('This variable might not be defined when this statement is executed.',
                      'possibly-undefined',
                      'Reported when a statement uses a variable that might not be assigned.'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    possibly_undefined = set()

    @check_messages('possibly-undefined')
    def visit_name(self, node):
        if self._check_possibly_undefined(node):
            self.add_message('possibly-undefined', node=node)

    def visit_module(self, node):
        self._analyze(node)

    def visit_functiondef(self, node):
        self._analyze(node)

    def _check_possibly_undefined(self, node: astroid.Name) -> bool:
        """Returns True if there exists a path from the start block to node where
        a variable used by node might not be defined."""
        b = node in self.possibly_undefined
        return b

    def _analyze(self, node: Union[astroid.Module, astroid.FunctionDef]) -> None:
        """Return a Tuple of
            (1) dictionary with key:value as CFGBlock:(in_set, out_set).
        """
        facts = {}
        blocks = self._get_blocks_rpo(node)

        all_assigns = self._get_assigns(blocks)
        for block in blocks:
            facts[block] = {}
            facts[block]['out'] = all_assigns.copy()

        worklist = blocks[:]
        while len(worklist) != 0:
            b = worklist.pop()
            outs = [facts[p.source]['out'] for p in b.predecessors]
            if outs == []:
                facts[b]['in'] = set()
            else:
                facts[b]['in'] = set.intersection(*outs)
            gen, kill = self.gen_and_kill(b)
            temp = gen.union(facts[b]['in'].difference(kill))
            if temp != facts[b]['out']:
                facts[b]['out'] = temp
                successors = set([succ.target for succ in b.successors])
                worklist = list(set(worklist).union(successors))

        for block in blocks:
            gen = set()
            kill = set()
            for statement in block.statements:
                if isinstance(statement, astroid.Assign):
                    gen.update(self._get_targets(statement))
                elif isinstance(statement, astroid.AnnAssign) and hasattr(
                        statement.target, 'name'):
                    gen.add(statement.target)
                elif isinstance(statement, astroid.Delete):
                    kill.update(self._get_targets(statement))
                self._analyze_statement(statement, gen.union(facts[block]['in'].difference(kill)), all_assigns)

    def gen_and_kill(self, block: CFGBlock) -> Tuple[Set[str], Set[str]]:
        gen = set()
        kill = set()
        for statement in block.statements:
            if isinstance(statement, astroid.Assign):
                gen.update(self._get_targets(statement))
            elif isinstance(statement, astroid.AnnAssign) and hasattr(statement.target, 'name'):
                gen.add(statement.target)
            elif isinstance(statement, astroid.Delete):
                kill.update(self._get_targets(statement))
        return gen, kill

    def _analyze_statement(self, node: NodeNG, facts: Set[str], vars: Set[str]):
        if isinstance(node, astroid.Name):
            name = node.name
            if name in vars and name not in facts and not self._is_function_name(node):
                self.possibly_undefined.add(node)
        else:
            for child in node.get_children():
                self._analyze_statement(child, facts, vars)

    def _get_targets(self, statement: Union[astroid.Assign, astroid.Delete]) -> Set[str]:
        targets = set()
        for target in statement.targets:
            try:
                # only AssignName node has a `name` attribute.
                targets.add(target.name)
            except AttributeError:
                pass
        return targets

    def _get_assigns(self, blocks: List[CFGBlock]) -> Set[str]:
        """Returns a set of all local and parameter variables that could be
        defined in the program (either a function or module).

        IF a variable 'v' is assigned in the function and there is no global/nonlocal
        statement applied to 'v' THEN 'v' is a local variable.
        """
        assigns = set()
        kills = set()
        for block in blocks:
            for statement in block.statements:
                if isinstance(statement, astroid.Arguments):
                    for arg in statement.args:
                        assigns.add(arg)
                elif isinstance(statement, astroid.Assign):
                    for target in statement.targets:
                        try:
                            assigns.add(target.name)
                        except AttributeError:
                            # exception raised if `target` is AssignAttr or Starred node
                            pass
                elif isinstance(statement, (astroid.Global, astroid.Nonlocal)):
                    for name in statement.names:
                        kills.add(name)

        return assigns.difference(kills)

    def _is_function_name(self, node: astroid.Name) -> bool:
        if isinstance(node.parent, astroid.Call) and node == node.parent.func:
            return True

    def _get_blocks_rpo(self, node: Union[astroid.Module, astroid.FunctionDef]) -> List[CFGBlock]:
        """Return the sequence of all blocks in this graph in the order of
        a reverse post-order traversal."""
        blocks = self._get_blocks(node.cfg_block, set())
        # blocks.reverse()
        return blocks

    def _get_blocks(self, block: CFGBlock, visited) -> List[CFGBlock]:
        if block.id in visited:
            return []
        elif block.successors == []:
            visited.add(block.id)
            return [block]
        else:
            visited.add(block.id)
            blocks = []
            for succ in block.successors:
                blocks.extend(self._get_blocks(succ.target, visited))
            blocks.append(block)
            return blocks


def register(linter):
    linter.register_checker(PossiblyUndefinedChecker(linter))
