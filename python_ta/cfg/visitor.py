import logging
from typing import Any, Dict, List, Optional, Tuple, Union

from astroid import extract_node, nodes
from astroid.exceptions import AstroidSyntaxError

from python_ta.contracts import parse_assertions

from .graph import CFGBlock, ControlFlowGraph


class CFGVisitor:
    """An astroid visitor that creates a control flow graph for a given Python module.

    Initialize with an options dict to configure the visitor.

    Supported Options:
      - "separate-condition-blocks": bool
            This option specifies whether the test condition of an if statement gets merged with any
            preceding statements or placed in a new block. By default, it will merge them.
      - "functions": list
            This option specifies whether to restrict the creation of cfgs to just top-level
            function definitions or methods provided in this list. By default, it will create the
            cfg for the file as it normally would.

    Private Attributes:
    _control_boundaries: A stack of the boundaries the visitor is currently in.
        The top of the stack corresponds to the end of the list.
        (compound statement [while], {'Break'/'Continue': CFGBlock to link to})
    """

    cfgs: Dict[Union[nodes.FunctionDef, nodes.Module], ControlFlowGraph]
    options: Dict[str, Any]
    # cfg_count is used as an "auto-increment" to ensure cfg ids are unique.
    cfg_count: int
    _current_cfg: Optional[ControlFlowGraph]
    _current_block: Optional[CFGBlock]
    _control_boundaries: List[Tuple[nodes.NodeNG, Dict[str, CFGBlock]]]
    z3_enabled: bool

    def __init__(self, options: Optional[Dict[str, Any]] = None, z3_enabled: bool = False) -> None:
        super().__init__()
        self.cfgs = {}
        self.options = {
            "separate-condition-blocks": False,
            "functions": [],
        }
        if options is not None:
            self.options.update(options)
        self.cfg_count = 0
        self._current_cfg = None
        self._current_block = None
        self._control_boundaries = []
        self.z3_enabled = z3_enabled

    def __getattr__(self, attr: str):
        if attr.startswith("visit_"):
            return self.visit_generic
        else:
            raise AttributeError(f"'CFGVisitor' object has no attribute '{attr}'")

    def visit_generic(self, node: nodes.NodeNG) -> None:
        """By default, add the expression to the end of the current block."""
        if self._current_block is not None:
            self._current_block.add_statement(node)

    def visit_module(self, module: nodes.Module) -> None:
        # Modules shouldn't be considered if user specifies functions to render
        functions_to_render = self.options.get("functions", [])
        if functions_to_render:
            for child in module.body:
                # Check any classes or function definitions for the target function/method
                if isinstance(child, nodes.FunctionDef) or isinstance(child, nodes.ClassDef):
                    child.accept(self)
            return

        self.cfgs[module] = ControlFlowGraph(self.cfg_count, z3_enabled=self.z3_enabled)
        self.cfg_count += 1
        self._current_cfg = self.cfgs[module]
        self._current_block = self._current_cfg.start
        module.cfg_block = self._current_cfg.start
        module.cfg = self._current_cfg

        for child in module.body:
            child.accept(self)

        self._current_cfg.link_or_merge(self._current_block, self._current_cfg.end)
        self._current_cfg.update_block_reachability()

    def visit_classdef(self, node: nodes.ClassDef) -> None:
        functions_to_render = self.options.get("functions", [])
        for child in node.body:
            if functions_to_render:
                if isinstance(child, nodes.FunctionDef):
                    child.accept(self)
            else:
                child.accept(self)

    def visit_functiondef(self, func: nodes.FunctionDef) -> None:
        # If user specifies to only render functions, check if the function/method name is listed
        functions_to_render = self.options.get("functions", [])
        scope_parent = func.scope().parent

        if functions_to_render:
            if (
                isinstance(scope_parent, nodes.ClassDef)
                and (scope_parent.name + "." + func.name) not in functions_to_render
            ) or (isinstance(scope_parent, nodes.Module) and func.name not in functions_to_render):
                return

        if self._current_block is not None:
            self._current_block.add_statement(func)

        previous_cfg = self._current_cfg
        previous_block = self._current_block

        self.cfgs[func] = ControlFlowGraph(self.cfg_count, z3_enabled=self.z3_enabled)
        self.cfg_count += 1
        self._current_cfg = self.cfgs[func]

        self._control_boundaries.append(
            (
                func,
                {
                    nodes.Return.__name__: self._current_cfg.end,
                    nodes.Raise.__name__: self._current_cfg.end,
                },
            )
        )

        # Current CFG block is self._current_cfg.start while initially creating the function cfg
        self._current_cfg.add_arguments(func.args)

        preconditions_node = _get_preconditions_node(func)

        self._current_block = self._current_cfg.create_block(
            self._current_cfg.start, edge_condition=preconditions_node
        )

        for child in func.body:
            child.accept(self)

        self._control_boundaries.pop()

        self._current_cfg.link_or_merge(self._current_block, self._current_cfg.end)
        self._current_cfg.update_block_reachability()

        if hasattr(func, "z3_constraints"):
            self._current_cfg.precondition_constraints = func.z3_constraints
            self._current_cfg.update_edge_z3_constraints()
            self._current_cfg.update_edge_feasibility()

        self._current_block = previous_block
        self._current_cfg = previous_cfg

    def visit_if(self, node: nodes.If) -> None:
        # When only creating cfgs for functions, _current_cfg will only be None outside of functions
        if self._current_cfg is None:
            return

        separate_conditions = self.options.get("separate-condition-blocks", False)
        if separate_conditions:
            # Create a block for the test condition
            test_block = self._current_cfg.create_block(self._current_block)
            test_block.add_statement(node.test)
            self._current_block = test_block
        else:
            # If the options doesn't specify to separate the test condition blocks, just add it to
            # the current block.
            self._current_block.add_statement(node.test)
        node.cfg_block = self._current_block
        old_curr = self._current_block

        # Handle "then" branch and label it.
        then_block = self._current_cfg.create_block(
            old_curr, edge_condition=node.test, edge_negate=False
        )
        self._current_block = then_block
        for child in node.body:
            child.accept(self)
        end_if = self._current_block

        # Handle "else" branch.
        if node.orelse == []:
            end_else = old_curr
        else:
            # Label the edge to the else block.
            else_block = self._current_cfg.create_block(
                old_curr, edge_condition=node.test, edge_negate=True
            )
            self._current_block = else_block
            for child in node.orelse:
                child.accept(self)
            end_else = self._current_block

        after_if_block = self._current_cfg.create_block()
        self._current_cfg.link_or_merge(end_if, after_if_block)
        # Label the edge if there was no "else" branch
        if node.orelse == []:
            self._current_cfg.link_or_merge(
                end_else,
                after_if_block,
                edge_condition=node.test,
                edge_negate=True,
            )
        else:
            self._current_cfg.link_or_merge(end_else, after_if_block)

        self._current_block = after_if_block

    def visit_while(self, node: nodes.While) -> None:
        # When only creating cfgs for functions, _current_cfg will only be None outside of functions
        if self._current_cfg is None:
            return

        old_curr = self._current_block

        # Handle "test" block
        test_block = self._current_cfg.create_block()
        test_block.add_statement(node.test)
        node.cfg_block = test_block
        self._current_cfg.link_or_merge(old_curr, test_block)

        after_while_block = self._current_cfg.create_block()

        # step into while
        self._control_boundaries.append(
            (
                node,
                {nodes.Break.__name__: after_while_block, nodes.Continue.__name__: test_block},
            )
        )

        # Handle "body" branch
        body_block = self._current_cfg.create_block(
            test_block, edge_condition=node.test, edge_negate=False
        )
        self._current_block = body_block
        for child in node.body:
            child.accept(self)
        end_body = self._current_block
        self._current_cfg.link_or_merge(end_body, test_block)

        # step out of while
        self._control_boundaries.pop()

        # Handle "else" branch
        else_block = self._current_cfg.create_block(
            test_block, edge_condition=node.test, edge_negate=True
        )
        self._current_block = else_block
        for child in node.orelse:
            child.accept(self)
        end_else = self._current_block

        self._current_cfg.link_or_merge(end_else, after_while_block)
        self._current_block = after_while_block

    def visit_for(self, node: nodes.For) -> None:
        # When only creating cfgs for functions, _current_cfg will only be None outside of functions
        if self._current_cfg is None:
            return

        old_curr = self._current_block
        old_curr.add_statement(node.iter)
        node.cfg_block = old_curr

        # Handle "test" block
        test_block = self._current_cfg.create_block()
        test_block.add_statement(node.target)
        self._current_cfg.link_or_merge(old_curr, test_block)

        after_for_block = self._current_cfg.create_block()

        # step into for
        self._control_boundaries.append(
            (node, {nodes.Break.__name__: after_for_block, nodes.Continue.__name__: test_block})
        )

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

    def visit_break(self, node: nodes.Break) -> None:
        self._visit_jump(node)

    def visit_continue(self, node: nodes.Continue) -> None:
        self._visit_jump(node)

    def visit_return(self, node: nodes.Return) -> None:
        self._visit_jump(node)

    def visit_raise(self, node: nodes.Raise) -> None:
        self._visit_jump(node)

    def _visit_jump(
        self, node: Union[nodes.Break, nodes.Continue, nodes.Return, nodes.Raise]
    ) -> None:
        # When only creating cfgs for functions, _current_cfg will only be None outside of functions
        if self._current_cfg is None:
            return

        old_curr = self._current_block
        unreachable_block = self._current_cfg.create_block()
        for boundary, exits in reversed(self._control_boundaries):
            if (
                isinstance(boundary, nodes.FunctionDef) or isinstance(boundary, nodes.ClassDef)
            ) and (isinstance(node, nodes.Break) or isinstance(node, nodes.Continue)):
                logging.warning(
                    f"'{type(node).__name__}' outside"
                    f' {"function" if isinstance(node, nodes.Return) else "loop"}'
                )
                self._current_cfg.link(old_curr, unreachable_block)
                old_curr.add_statement(node)
                break

            if isinstance(node, nodes.Raise):
                exc_name = _get_raise_exc(node)

                if exc_name in exits:
                    self._current_cfg.link(old_curr, exits[exc_name])
                    old_curr.add_statement(node)
                    break

            if type(node).__name__ in exits:
                self._current_cfg.link(old_curr, exits[type(node).__name__])
                old_curr.add_statement(node)
                break

        else:
            logging.warning(
                f"'{type(node).__name__}' outside"
                f' {"function" if isinstance(node, nodes.Return) else "loop"}'
            )
            self._current_cfg.link(old_curr, unreachable_block)
            old_curr.add_statement(node)

        self._current_block = unreachable_block

    def visit_try(self, node: nodes.Try) -> None:
        # When only creating cfgs for functions, _current_cfg will only be None outside of functions
        if self._current_cfg is None:
            return

        if self._current_block.statements != []:
            self._current_block = self._current_cfg.create_block(self._current_block)

        node.cfg_block = self._current_block

        # Construct the exception handlers first
        # Initialize a temporary block to later merge with end_body
        self._current_block = self._current_cfg.create_block()
        temp = self._current_block
        end_block = self._current_cfg.create_block()
        # Case where Raise is not handled in try
        self._control_boundaries.append((node, {nodes.Raise.__name__: end_block}))
        cbs_added = 1

        after_body = []
        # Construct blocks in reverse to give precedence to the first block in overlapping except
        # branches
        for handler in reversed(node.handlers):
            h = self._current_cfg.create_block()
            self._current_block = h
            handler.cfg_block = h

            exceptions = _extract_exceptions(handler)
            # Edge case: catch-all except clause (i.e. except: ...)
            if exceptions == []:
                self._control_boundaries.append((node, {nodes.Raise.__name__: h}))
                cbs_added += 1

            # General case: specific except clause
            for exception in exceptions:
                self._control_boundaries.append((node, {f"{nodes.Raise.__name__} {exception}": h}))
                cbs_added += 1

            if handler.name is not None:  # The name assigned to the caught exception.
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

        # Construct the try body so reset current block to this node's block
        self._current_block = node.cfg_block

        for child in node.body:
            child.accept(self)
        end_body = self._current_block

        # Remove each control boundary that we added in this method
        for _ in range(cbs_added):
            self._control_boundaries.pop()

        self._current_cfg.link_or_merge(temp, end_body)
        self._current_cfg.multiple_link_or_merge(end_body, after_body)
        self._current_block = end_block

    def visit_with(self, node: nodes.With) -> None:
        # When only creating cfgs for functions, _current_cfg will only be None outside of functions
        if self._current_cfg is None:
            return

        for context_node, name in node.items:
            self._current_block.add_statement(context_node)
            if name is not None:
                self._current_block.add_statement(name)

        for child in node.body:
            child.accept(self)

    def visit_match(self, node: nodes.Match) -> None:
        """Visit a match statement and create appropriate control flow."""
        # When only creating cfgs for functions, _current_cfg will only be None outside of functions
        if self._current_cfg is None:
            return

        self._current_block.add_statement(node.subject)
        node.cfg_block = self._current_block
        after_match_block = self._current_cfg.create_block()

        case_end_blocks = []

        prev_case = self._current_block
        connect_guard_block = False

        for case in node.cases:
            edge_label = "No Match" if case_end_blocks else ""

            separate_conditions = self.options.get("separate-condition-blocks", False)

            pattern_block = self._current_cfg.create_block(prev_case, edge_label=edge_label)
            pattern_block.add_statement(case.pattern)

            if connect_guard_block:
                self._current_cfg.link_or_merge(guard_block, pattern_block, edge_label="False")
                connect_guard_block = False

            if separate_conditions and case.guard is not None:
                guard_block = self._current_cfg.create_block(pattern_block, edge_label="Match")
                guard_block.add_statement(case.guard)
                pattern_body = self._current_cfg.create_block(guard_block, edge_label="True")
                connect_guard_block = True
            else:
                if not separate_conditions and case.guard is not None:
                    pattern_block.add_statement(case.guard)
                pattern_body = self._current_cfg.create_block(pattern_block, edge_label="Match")

            self._current_block = pattern_body

            for child in case.body:
                child.accept(self)

            case_end_blocks.append(self._current_block)
            prev_case = pattern_block

        # For the final block, create a new block that links to the end of the match
        self._current_cfg.link_or_merge(pattern_block, after_match_block, edge_label="No Match")
        if connect_guard_block:
            self._current_cfg.link_or_merge(guard_block, after_match_block, edge_label="False")

        for end_block in case_end_blocks:
            self._current_cfg.link_or_merge(end_block, after_match_block)

        self._current_block = after_match_block


def _extract_exceptions(node: nodes.ExceptHandler) -> List[str]:
    """A helper method that returns a list of all the exceptions handled by this except block as a
    list of strings.
    """
    exceptions = node.type
    exceptions_so_far = []
    # ExceptHandler.type will either be Tuple, NodeNG, or None.
    if exceptions is None:
        return exceptions_so_far

    # Get all the Name nodes for all exceptions this except block is handling
    for exception in exceptions.nodes_of_class(nodes.Name):
        exceptions_so_far.append(exception.name)

    return exceptions_so_far


def _get_raise_exc(node: nodes.Raise) -> str:
    """A helper method that returns a string formatted for the control boundary representing the
    exception that this Raise node throws.

    Preconditions:
        - the raise statement is of the form 'raise' or 'raise <exception_class>'
    """
    exceptions = node.nodes_of_class(nodes.Name)

    # Return the formatted name of the exception or the just 'Raise' otherwise
    try:
        return f"{nodes.Raise.__name__} {next(exceptions).name}"
    except StopIteration:
        return nodes.Raise.__name__


def _get_preconditions_node(func: nodes.FunctionDef) -> Optional[nodes.NodeNG]:
    """A helper method that takes in a function definition node, retrieves its preconditions, and then parses them
    into a AST node representing all the valid Python preconditions combined in an and statement. Returns None if
    there are no valid Python preconditions."""
    valid_assertions = [
        assertion for assertion in parse_assertions(func) if _is_python_precondition(assertion)
    ]
    if not valid_assertions:
        return None
    precondition_string = " and ".join(valid_assertions)
    condition = extract_node(precondition_string)
    return condition


def _is_python_precondition(precondition: str) -> bool:
    """Given a precondition string, determine if it is a valid Python precondition that can be parsed and return
    a boolean result."""
    try:
        _ = extract_node(precondition)
        return True
    except (AstroidSyntaxError, ValueError):  # ValueError raised when precondition is blank
        return False
