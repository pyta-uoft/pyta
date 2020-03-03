import astroid
from astroid.node_classes import NodeNG
from .graph import ControlFlowGraph, CFGBlock
from typing import List, Tuple, Dict, Union, Optional


class CFGVisitor:
    """An astroid visitor that creates a control flow graph for a given Python module.

    Private Attributes:
    _control_boundaries: A stack of the boundaries the visitor is currently in.
        The top of the stack corresponds to the end of the list.
        (compound statement [while], {'Break'/'Continue': CFGBlock to link to})
    """
    cfgs: Dict[Union[astroid.FunctionDef, astroid.Module], ControlFlowGraph]
    _current_cfg: Optional[ControlFlowGraph]
    _current_block: Optional[CFGBlock]
    _control_boundaries: List[Tuple[NodeNG, Dict[str, CFGBlock]]]

    def __init__(self) -> None:
        super().__init__()
        self.cfgs = {}
        self._current_cfg = None
        self._current_block = None
        self._control_boundaries = []

    def __getattr__(self, attr: str):
        if attr.startswith('visit_'):
            return self.visit_generic
        else:
            raise AttributeError(f"'CFGVisitor' object has not attribute '{attr}'")

    def visit_generic(self, node: NodeNG) -> None:
        """By default, add the expression to the end of the current block."""
        self._current_block.add_statement(node)

    def visit_module(self, module: astroid.Module) -> None:
        self.cfgs[module] = ControlFlowGraph()
        self._current_cfg = self.cfgs[module]
        self._current_block = self._current_cfg.start
        module.cfg_block = self._current_cfg.start

        for child in module.body:
            child.accept(self)

        self._current_cfg.link_or_merge(self._current_block, self._current_cfg.end)
        self._current_cfg.update_block_reachability()

    def visit_classdef(self, node: astroid.ClassDef) -> None:
        for child in node.body:
            child.accept(self)

    def visit_functiondef(self, func: astroid.FunctionDef) -> None:
        self._current_block.add_statement(func)

        previous_cfg = self._current_cfg
        previous_block = self._current_block

        self.cfgs[func] = ControlFlowGraph()
        self._current_cfg = self.cfgs[func]

        self._control_boundaries.append((func, {astroid.Return.__name__: self._current_cfg.end}))

        self._current_cfg.start.add_statement(func.args)
        func.cfg_block = self._current_cfg.start

        self._current_block = self._current_cfg.create_block(self._current_cfg.start)

        for child in func.body:
            child.accept(self)

        self._control_boundaries.pop()

        self._current_cfg.link_or_merge(self._current_block, self._current_cfg.end)
        self._current_cfg.update_block_reachability()

        self._current_block = previous_block
        self._current_cfg = previous_cfg

    def visit_if(self, node: astroid.If) -> None:
        self._current_block.add_statement(node.test)
        node.cfg_block = self._current_block
        old_curr = self._current_block

        # Handle "then" branch.
        then_block = self._current_cfg.create_block(old_curr)
        self._current_block = then_block
        for child in node.body:
            child.accept(self)
        end_if = self._current_block

        # Handle "else" branch.
        if node.orelse == []:
            end_else = old_curr
        else:
            else_block = self._current_cfg.create_block(old_curr)
            self._current_block = else_block
            for child in node.orelse:
                child.accept(self)
            end_else = self._current_block

        after_if_block = self._current_cfg.create_block()
        self._current_cfg.link_or_merge(end_if, after_if_block)
        self._current_cfg.link_or_merge(end_else, after_if_block)

        self._current_block = after_if_block

    def visit_while(self, node: astroid.While) -> None:
        old_curr = self._current_block

        # Handle "test" block
        test_block = self._current_cfg.create_block()
        test_block.add_statement(node.test)
        node.cfg_block = test_block
        self._current_cfg.link_or_merge(old_curr, test_block)

        after_while_block = self._current_cfg.create_block()

        # step into while
        self._control_boundaries.append((node, {astroid.Break.__name__: after_while_block,
                                                astroid.Continue.__name__: test_block}))

        # Handle "body" branch
        body_block = self._current_cfg.create_block(test_block)
        self._current_block = body_block
        for child in node.body:
            child.accept(self)
        end_body = self._current_block
        self._current_cfg.link_or_merge(end_body, test_block)

        # step out of while
        self._control_boundaries.pop()

        # Handle "else" branch
        else_block = self._current_cfg.create_block(test_block)
        self._current_block = else_block
        for child in node.orelse:
            child.accept(self)
        end_else = self._current_block

        self._current_cfg.link_or_merge(end_else, after_while_block)
        self._current_block = after_while_block

    def visit_for(self, node: astroid.For) -> None:
        old_curr = self._current_block
        old_curr.add_statement(node.iter)
        node.cfg_block = old_curr

        # Handle "test" block
        test_block = self._current_cfg.create_block()
        test_block.add_statement(node.target)
        self._current_cfg.link_or_merge(old_curr, test_block)

        after_for_block = self._current_cfg.create_block()

        # step into for
        self._control_boundaries.append((node, {astroid.Break.__name__: after_for_block,
                                                astroid.Continue.__name__: test_block}))

        # Handle "body" branch
        body_block = self._current_cfg.create_block(test_block)
        self._current_block = body_block
        for child in node.body:
            child.accept(self)
        end_body = self._current_block
        self._current_cfg.link_or_merge(end_body, test_block)

        # step out of for
        self._control_boundaries.pop()

        # Handle "else" branch
        else_block = self._current_cfg.create_block(test_block)
        self._current_block = else_block
        for child in node.orelse:
            child.accept(self)
        end_else = self._current_block

        self._current_cfg.link_or_merge(end_else, after_for_block)
        self._current_block = after_for_block

    def visit_break(self, node: astroid.Break) -> None:
        self._visit_jump(node)

    def visit_continue(self, node:astroid.Continue) -> None:
        self._visit_jump(node)

    def visit_return(self, node: astroid.Return) -> None:
        self._visit_jump(node)

    def _visit_jump(self, node: Union[astroid.Break, astroid.Continue, astroid.Return]) -> None:
        old_curr = self._current_block
        for boundary, exits in reversed(self._control_boundaries):
            if type(node).__name__ in exits:
                self._current_cfg.link(old_curr, exits[type(node).__name__])
                old_curr.add_statement(node)
                break
        else:
            raise SyntaxError(f'\'{type(node).__name__}\' outside'
                              f' {"function" if isinstance(node, astroid.Return) else "loop"}')
        unreachable_block = self._current_cfg.create_block()
        self._current_block = unreachable_block

    def visit_tryexcept(self, node: astroid.TryExcept) -> None:
        if self._current_block.statements != []:
            self._current_block = self._current_cfg.create_block(self._current_block)

        node.cfg_block = self._current_block

        for child in node.body:
            child.accept(self)
        end_body = self._current_block

        end_block = self._current_cfg.create_block()

        after_body = []
        for handler in node.handlers:
            h = self._current_cfg.create_block()
            self._current_block = h
            handler.cfg_block = h
            if handler.name is not None:   # The name assigned to the caught exception.
                handler.name.accept(self)
            for child in handler.body:
                child.accept(self)
            end_handler = self._current_block
            self._current_cfg.link_or_merge(end_handler, end_block)
            after_body.append(h)

        if node.orelse == []:
            after_body.append(end_block)
        else:
            self._current_block = self._current_cfg.create_block()
            after_body.append(self._current_block)
            for child in node.orelse:
                child.accept(self)
            self._current_cfg.link_or_merge(self._current_block, end_block)

        self._current_cfg.multiple_link_or_merge(end_body, after_body)
        self._current_block = end_block

    def visit_with(self, node: astroid.With) -> None:
        for context_node, name in node.items:
            self._current_block.add_statement(context_node)
            if name is not None:
                self._current_block.add_statement(name)

        for child in node.body:
            child.accept(self)
