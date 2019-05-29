import astroid
from astroid.node_classes import NodeNG
from .graph import ControlFlowGraph, CFGBlock
from typing import List, Tuple


class CFGVisitor:
    """An astroid visitor that creates a control flow graph for a given Python module.

    Private Attributes:
        _scope: A stack of the scopes the visitor is in. The top element refers
                to the current scope. (scope_type [for, while],  start_block, end_block)
    """
    cfg: ControlFlowGraph
    _current_block: CFGBlock
    _scope: List[Tuple[str, CFGBlock, CFGBlock]]

    def __init__(self) -> None:
        super().__init__()
        self.cfg = ControlFlowGraph()
        self._current_block = self.cfg.start
        self._scope = []

    def __getattr__(self, attr: str):
        if attr.startswith('visit_'):
            return self.visit_generic
        else:
            raise AttributeError(f"'CFGVisitor' object has not attribute '{attr}'")

    def visit_generic(self, node: NodeNG) -> None:
        """By default, add the expression to the end of the current block."""
        self._current_block.statements.append(node)

    def visit_module(self, module: astroid.Module) -> None:
        self.cfg = ControlFlowGraph()
        self._current_block = self.cfg.start

        for child in module.body:
            child.accept(self)
        self._link_or_merge(self._current_block, self.cfg.end)

    def visit_if(self, node: astroid.If) -> None:
        self._current_block.statements.append(node.test)
        old_curr = self._current_block

        # Handle "then" branch.
        then_block = self.cfg.create_block(old_curr)
        self._current_block = then_block
        for child in node.body:
            child.accept(self)
        end_if = self._current_block

        # Handle "else" branch.
        if node.orelse == []:
            end_else = old_curr
        else:
            else_block = self.cfg.create_block(old_curr)
            self._current_block = else_block
            for child in node.orelse:
                child.accept(self)
            end_else = self._current_block

        after_if_block = self.cfg.create_block()
        self._link_or_merge(end_if, after_if_block)
        self._link_or_merge(end_else, after_if_block)

        self._current_block = after_if_block

    def visit_while(self, node: astroid.While) -> None:
        old_curr = self._current_block

        # Handle "test" block
        # condition implies old_curr = empty start node
        if old_curr.statements == [] and old_curr.predecessors == []:
            old_curr.statements.append(node.test)
            test_block = old_curr
        else:
            test_block = self.cfg.create_block()
            test_block.statements.append(node.test)
            self.cfg.link_or_merge(old_curr, test_block)

        after_while_block = self.cfg.create_block()

        # enter `while` scope
        self._scope.append(("while", self._current_block, after_while_block))

        # Handle "body" branch
        body_block = self.cfg.create_block(test_block)
        self._current_block = body_block
        for child in node.body:
            child.accept(self)
        end_body = self._current_block
        self._link_or_merge(end_body, test_block)

        # Handle "else" branch
        else_block = self.cfg.create_block(test_block)
        self._current_block = else_block
        for child in node.orelse:
            child.accept(self)
        end_else = self._current_block

        self._link_or_merge(end_else, after_while_block)
        self._current_block = after_while_block

        # exit `while` scope
        self._scope.pop()

    def visit_break(self, node: astroid.Break) -> None:
        self._current_block.statements.append(node)
        old_curr = self._current_block
        for i in reversed(range(len(self._scope))):
            if self._scope[i][0] == 'while':
                after_loop_block = self._scope[i][2]
                self.cfg.link_or_merge(old_curr, after_loop_block)
                return
        raise SyntaxError('\'break\' outside loop')

    def _has_break(self, block: CFGBlock) -> bool:
        """Returns True if the block contains the keyword 'break'"""
        return any((isinstance(n, astroid.Break) for n in block.statements))

    def _link_or_merge(self, source: CFGBlock, target: CFGBlock) -> None:
        if not self._has_break(source):
            self.cfg.link_or_merge(source, target)
