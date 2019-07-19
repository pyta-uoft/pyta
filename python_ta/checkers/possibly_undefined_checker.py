"""checker for variables that might not be defined in the program.
"""
from typing import Union
import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from python_ta.cfg.graph import CFGBlock
from astroid.node_classes import NodeNG
from typing import Set, List


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
        return node in self.possibly_undefined

    def _analyze(self, node: Union[astroid.Module, astroid.FunctionDef]) -> None:
        """Runs the data flow algorithm on a `Module` or `Function` CFG, which in turn
        appends `Name` nodes to `possibly_undefined` if it might not be defined.
        """
        facts = {}
        blocks = self._get_blocks_po(node)

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
            temp = self._transfer(b, facts[b]['in'], all_assigns)
            if temp != facts[b]['out']:
                facts[b]['out'] = temp
                successors = set([succ.target for succ in b.successors])
                worklist = list(set(worklist).union(successors))

    def _transfer(self, block: CFGBlock, in_facts: Set[str], all_assigns: Set[str]) -> Set[str]:
        gen = set()
        kill = set()
        for statement in block.statements:
            if isinstance(statement, astroid.Assign):
                gen.update(self._get_targets(statement))
            elif isinstance(statement, astroid.AnnAssign) and hasattr(statement.target, 'name'):
                gen.add(statement.target)
            elif isinstance(statement, astroid.Delete):
                kill.update(self._get_targets(statement))
            self._analyze_statement(statement, gen.union(in_facts.difference(kill)), all_assigns)
        return gen.union(in_facts.difference(kill))

    def _analyze_statement(self, node: NodeNG, facts: Set[str], local_vars: Set[str]) -> None:
        if isinstance(node, astroid.Name):
            name = node.name
            if name in local_vars and name not in facts and not self._is_function_name(node):
                self.possibly_undefined.add(node)
            elif node in self.possibly_undefined:
                self.possibly_undefined.remove(node)
        else:
            for child in node.get_children():
                self._analyze_statement(child, facts, local_vars)

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

        IF a variable 'v' is defined in the function and there is no global/nonlocal
        statement applied to 'v' THEN 'v' is a local variable.

        Note that `local` in the context of a module level analysis, refers to global
        variables.
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

    def _get_blocks_po(self, node: Union[astroid.Module, astroid.FunctionDef]) -> List[CFGBlock]:
        """Return the sequence of all blocks in this graph in the order of
        a post-order traversal."""
        return self._get_blocks(node.cfg_block, set())

    def _get_blocks(self, block: CFGBlock, visited) -> List[CFGBlock]:
        if block.id in visited:
            return []
        else:
            visited.add(block.id)
            blocks = []
            for succ in block.successors:
                blocks.extend(self._get_blocks(succ.target, visited))
            blocks.append(block)
            return blocks


def register(linter):
    linter.register_checker(PossiblyUndefinedChecker(linter))
