"""checker for variables that might not be defined in the program.
"""
from typing import Union, Generator
import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker, utils
from pylint.checkers.utils import check_messages
from python_ta.cfg.graph import CFGBlock, ControlFlowGraph
from typing import Set
from itertools import chain

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

    def __init__(self, linter=None):
        super().__init__(linter=linter)
        self._possibly_undefined: Set[astroid.Name] = set()

    @check_messages('possibly-undefined')
    def visit_name(self, node):
        """Adds message if there exists a path from the start block to node where
        a variable used by node might not be defined."""
        if node in self._possibly_undefined:
            self.add_message('possibly-undefined', node=node)

    def visit_module(self, node):
        self._analyze(node)

    def visit_functiondef(self, node):
        self._analyze(node)

    def _analyze(self, node: Union[astroid.Module, astroid.FunctionDef]) -> None:
        """Runs the data flow algorithm on a `Module` or `Function` CFG, which in turn
        appends `Name` nodes to `self.possibly_undefined` if it might not be defined.

        Data flow algorithms retrieved from:
        https://www.seas.harvard.edu/courses/cs252/2011sp/slides/Lec02-Dataflow.pdf#page=31
        """
        out_facts = {}
        cfg = ControlFlowGraph()
        cfg.start = node.cfg_block
        blocks = list(cfg.get_blocks_postorder())
        blocks.reverse()

        all_assigns = self._get_assigns(node)
        for block in blocks:
            out_facts[block] = all_assigns.copy()

        worklist = blocks
        while len(worklist) != 0:
            b = worklist.pop()
            outs = [out_facts[p.source] for p in b.predecessors if p.source in out_facts]
            if outs == []:
                in_facts = set()
            else:
                in_facts = set.intersection(*outs)
            temp = self._transfer(b, in_facts, all_assigns)
            if temp != out_facts[b]:
                out_facts[b] = temp
                worklist.extend([succ.target for succ in b.successors])

    def _transfer(self, block: CFGBlock, in_facts: Set[str], local_vars: Set[str]) -> Set[str]:
        gen = in_facts.copy()
        kill = set()
        for statement in block.statements:
            if isinstance(statement, astroid.FunctionDef):
                continue
            for node in self.get_nodes(statement):
                if isinstance(node, astroid.AssignName):
                    gen.add(node.name)
                elif isinstance(node, astroid.DelName):
                    kill.add(node.name)
                else:
                    name = node.name
                    # comment out 'self.config....' check when running tests
                    if not (name in astroid.Module.scope_attrs or utils.is_builtin(name)) \
                            and name in local_vars \
                            and name not in gen.difference(kill):
                        self._possibly_undefined.add(node)
                    elif node in self._possibly_undefined:
                        self._possibly_undefined.remove(node)
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
        for statement in node.nodes_of_class((astroid.Nonlocal, astroid.Global,
                                              astroid.ImportFrom, astroid.Import), astroid.FunctionDef):
            for name in statement.names:
                if type(name) is tuple:
                    # name[1] is the alias of the imported object/var name[0]
                    # name[1] == str or None
                    name = name[1] or name[0]
                kills.add(name)

        return assigns.difference(kills)

    def get_nodes(self, statement: astroid.node_classes.NodeNG) -> Generator[astroid.node_classes.NodeNG, None, None]:
        multiple_nodes = lambda nodes : chain.from_iterable(self.get_nodes(node) for node in nodes)
        if isinstance(statement, astroid.Assign):
            # RHS is evaluated before assigned in an assignment statement
            yield from self.get_nodes(statement.value)
            yield from multiple_nodes(statement.targets) # statement.targets is a list of nodes
        elif isinstance(statement, (astroid.ListComp, astroid.SetComp, astroid.DictComp, astroid.GeneratorExp)):
            # Comprehension targets are assigned before expression is evaluated.
            yield from multiple_nodes(statement.generators)  # statement.generators is a list of nodes
            if not hasattr(statement, 'elt'):
                yield from self.get_nodes(statement.key) # keys evaluated first
                yield from self.get_nodes(statement.value)
            else:
                yield from self.get_nodes(statement.elt)
        else:
            yield from statement.nodes_of_class((astroid.AssignName, astroid.DelName, astroid.Name),
                                                astroid.FunctionDef)

def register(linter):
    linter.register_checker(PossiblyUndefinedChecker(linter))
