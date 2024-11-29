from __future__ import annotations

from typing import Any, Dict, Generator, List, Optional, Set

try:
    from z3 import (
        Z3_OP_UNINTERPRETED,
        ExprRef,
        Not,
        Solver,
        Z3Exception,
        is_const,
        unsat,
    )

    from ..z3.z3_parser import Z3ParseException, Z3Parser

    z3_dependency_available = True
except ImportError:
    ExprRef = Any
    Z3Parser = Any
    Not = Any
    Z3Exception = Any
    is_const = Any
    Z3_OP_UNINTERPRETED = Any
    Z3ParseException = Any
    Solver = Any
    unsat = Any
    z3_dependency_available = False

from astroid import (
    AnnAssign,
    Arguments,
    Assign,
    AssignName,
    AugAssign,
    Break,
    Continue,
    NodeNG,
    Raise,
    Return,
)


class ControlFlowGraph:
    """A graph representing the control flow of a Python program."""

    start: CFGBlock
    end: CFGBlock
    # The unique id of this cfg. Defaults to 0 if not initialized in a CFGVisitor instance.
    cfg_id: int
    # block_count is used as an "autoincrement" to ensure the block ids are unique.
    block_count: int
    # blocks (with at least one statement) that will never be executed in runtime.
    unreachable_blocks: Set[CFGBlock]
    # z3 constraints of preconditions
    precondition_constraints: List[ExprRef]
    # map from variable names to z3 variables
    _z3_vars: Dict[str, ExprRef]

    def __init__(self, cfg_id: int = 0) -> None:
        self.block_count = 0
        self.cfg_id = cfg_id
        self.unreachable_blocks = set()
        self.start = self.create_block()
        self.end = self.create_block()
        self._z3_vars = {}
        self.precondition_constraints = []

    def add_arguments(self, args: Arguments) -> None:
        self.start.add_statement(args)
        args.parent.cfg = self
        args.parent.cfg_block = self.start

        if ExprRef is not Any:
            # Parse types
            parser = Z3Parser()
            z3_vars = parser.parse_arguments(args)
            self._z3_vars.update(z3_vars)

    def create_block(
        self,
        pred: Optional[CFGBlock] = None,
        edge_label: Optional[Any] = None,
        edge_condition: Optional[NodeNG] = None,
        edge_negate: Optional[bool] = None,
    ) -> CFGBlock:
        """Create a new CFGBlock for this graph.

        If pred is specified, set that block as a predecessor of the new block.

        If edge_label is specified, set the corresponding edge in the CFG with that label.

        If edge_condition is specified, store the condition node in the corresponding edge.

        edge_negate is not None only if edge_condition is specified
        """
        new_block = CFGBlock(self.block_count)
        self.unreachable_blocks.add(new_block)

        self.block_count += 1
        if pred:
            self.link_or_merge(pred, new_block, edge_label, edge_condition, edge_negate)
        return new_block

    def link(self, source: CFGBlock, target: CFGBlock) -> None:
        """Link source to target."""
        if not source.is_jump():
            CFGEdge(source, target)

    def link_or_merge(
        self,
        source: CFGBlock,
        target: CFGBlock,
        edge_label: Optional[Any] = None,
        edge_condition: Optional[NodeNG] = None,
        edge_negate: Optional[bool] = None,
    ) -> None:
        """Link source to target, or merge source into target if source is empty.

        An "empty" node for this purpose is when source has no statements.

        source with a jump statement cannot be further linked or merged to
        another target.

        If edge_label is specified, set the corresponding edge in the CFG with that label.

        If edge_condition is specified, store the condition node in the corresponding edge.

        edge_negate is not None only if edge_condition is specified
        """
        if source.is_jump():
            return
        if source.statements == []:
            if source is self.start:
                self.start = target
            else:
                for edge in source.predecessors:
                    edge.target = target
                    target.predecessors.append(edge)
            # source is a utility block that helps build the cfg that does not
            # represent any part of the program so it is redundant.
            self.unreachable_blocks.remove(source)
        else:
            CFGEdge(source, target, edge_label, edge_condition, edge_negate)

    def multiple_link_or_merge(self, source: CFGBlock, targets: List[CFGBlock]) -> None:
        """Link source to multiple target, or merge source into targets if source is empty.

        An "empty" node for this purpose is when source has no statements.

        source with a jump statement cannot be further linked or merged to
        another target.

        Precondition:
            - source != cfg.start
        """
        if source.statements == []:
            for edge in source.predecessors:
                for t in targets:
                    CFGEdge(edge.source, t)
                edge.source.successors.remove(edge)
            source.predecessors = []
            self.unreachable_blocks.remove(source)
        else:
            for target in targets:
                self.link(source, target)

    def get_blocks(self, only_feasible: bool = False) -> Generator[CFGBlock, None, None]:
        """Generate a sequence of all blocks in this graph.

        When only_feasible is True, only generate blocks feasible from start based on edge z3 constraints.
        """
        yield from self._get_blocks(self.start, set(), only_feasible)

    def _get_blocks(
        self, block: CFGBlock, visited: Set[int], only_feasible: bool
    ) -> Generator[CFGBlock, None, None]:
        if block.id in visited:
            return

        yield block
        visited.add(block.id)

        for edge in block.successors:
            if not only_feasible or edge.is_feasible:
                yield from self._get_blocks(edge.target, visited, only_feasible)

    def get_blocks_postorder(self, only_feasible: bool = False) -> Generator[CFGBlock, None, None]:
        """Return the sequence of all blocks in this graph in the order of
        a post-order traversal.

        When only_feasible is True, only generate blocks feasible from start based on edge z3 constraints.
        """
        yield from self._get_blocks_postorder(self.start, set(), only_feasible)

    def _get_blocks_postorder(
        self, block: CFGBlock, visited: Set[int], only_feasible: bool
    ) -> Generator[CFGBlock, None, None]:
        if block.id in visited:
            return

        visited.add(block.id)
        for succ in block.successors:
            if not only_feasible or succ.is_feasible:
                yield from self._get_blocks_postorder(succ.target, visited, only_feasible)

        yield block

    def get_edges(self) -> Generator[CFGEdge, None, None]:
        """Generate a sequence of all edges in this graph."""
        yield from self._get_edges(self.start, set())

    def _get_edges(self, block: CFGBlock, visited: Set[int]) -> Generator[CFGEdge, None, None]:
        if block.id in visited:
            return

        visited.add(block.id)

        for edge in block.successors:
            yield edge
            yield from self._get_edges(edge.target, visited)

    def get_paths(self) -> List[List[CFGEdge]]:
        """Get edges that represent paths from start to end node in depth-first order."""
        paths = []

        def _dfs(
            current_edge: CFGEdge,
            current_path: List[CFGEdge],
            visited_edges: Set[CFGEdge],
            visited_nodes: Set[CFGBlock],
        ):
            if current_edge in visited_edges:
                return

            visited_edges.add(current_edge)
            current_path.append(current_edge)
            visited_nodes.add(current_edge.source)

            if (
                current_edge.target == self.end
                or current_edge.target in visited_nodes
                or set(current_edge.target.successors).issubset(visited_edges)
            ):
                paths.append(current_path.copy())
            else:
                for edge in current_edge.target.successors:
                    _dfs(edge, current_path, visited_edges, visited_nodes)

            current_path.pop()
            visited_edges.remove(current_edge)
            visited_nodes.remove(current_edge.source)

        _dfs(self.start.successors[0], [], set(), set())
        return paths

    def update_block_reachability(self) -> None:
        for block in self.get_blocks():
            block.reachable = True
            if block in self.unreachable_blocks:
                self.unreachable_blocks.remove(block)

    def update_edge_z3_constraints(self) -> None:
        """Traverse through edges and add Z3 constraints on each edge.

        Constraints are generated from:
        - Function preconditions
        - If conditions
        - While conditions

        Constraints with reassigned variables are not included in subsequent edges.
        """
        if not z3_dependency_available:
            return

        for path_id, path in enumerate(self.get_paths()):
            # starting a new path
            z3_environment = Z3Environment(self._z3_vars, self.precondition_constraints)
            for edge in path:
                # traverse through edge
                if edge.condition is not None:
                    condition_z3_constraint = z3_environment.parse_constraint(edge.condition)
                    if condition_z3_constraint is not None:
                        if edge.negate is not None:
                            z3_environment.add_constraint(
                                Not(condition_z3_constraint)
                                if edge.negate
                                else condition_z3_constraint
                            )

                edge.z3_constraints[path_id] = z3_environment.update_constraints()

                # traverse into target node
                for node in edge.target.statements:
                    if isinstance(node, (Assign, AugAssign, AnnAssign)):
                        self._handle_variable_reassignment(node, z3_environment)

    def _handle_variable_reassignment(self, node: NodeNG, env: Z3Environment) -> None:
        """Check for reassignment statements and invoke Z3 environment"""
        if isinstance(node, Assign):
            for target in node.targets:
                if isinstance(target, AssignName):
                    env.assign(target.name)
        elif isinstance(node, (AugAssign, AnnAssign)):
            env.assign(node.target.name)

    def update_edge_feasibility(self) -> None:
        """Traverse through edges in DFS order and update is_feasible
        attribute of each edge. Edges that are unreachable with the given
        set of Z3 constraints will have is_feasible set to False
        """
        if not z3_dependency_available:
            return

        def _check_unsat(constraints: List[ExprRef]) -> bool:
            solver = Solver()
            solver.add(constraints)
            return solver.check() == unsat

        for edge in self.get_edges():
            if len(edge.z3_constraints) > 0:
                edge.is_feasible = not all(
                    _check_unsat(constraints) for constraints in edge.z3_constraints.values()
                )


class CFGBlock:
    """A node in a control flow graph.

    Represents a maximal block of code whose statements are guaranteed to execute in sequence.
    """

    # A unique identifier
    id: int
    # The statements in this block.
    statements: List[NodeNG]
    # This block's in-edges (from blocks that can execute immediately before this one).
    predecessors: List[CFGEdge]
    # This block's out-edges (to blocks that can execute immediately after this one).
    successors: List[CFGEdge]
    # Whether there exists a path from the start block to this block.
    reachable: bool

    def __init__(self, id_: int) -> None:
        """Initialize a new CFGBlock."""
        self.id = id_
        self.statements = []
        self.predecessors = []
        self.successors = []
        self.reachable = False

    def add_statement(self, statement: NodeNG) -> None:
        if not self.is_jump():
            self.statements.append(statement)
            statement.cfg_block = self

    @property
    def jump(self) -> Optional[NodeNG]:
        if len(self.statements) > 0:
            return self.statements[-1]

    @property
    def is_feasible(self) -> bool:
        return any(edge.is_feasible for edge in self.predecessors)

    def is_jump(self) -> bool:
        """Returns True if the block has a statement that branches
        the control flow (ex: `break`)"""
        return isinstance(self.jump, (Break, Continue, Return, Raise))


class CFGEdge:
    """An edge in a control flow graph.

    Edges are directed, and in the future may be augmented with auxiliary metadata about the control flow.

    The condition attribute stores the AST node representing the condition tested in If and While statements.
    The negate attribute stores the condition should be False (when `negate` is True) or condition should be true
    (when `negate` is False)
    """

    source: CFGBlock
    target: CFGBlock
    label: Optional[str]
    condition: Optional[NodeNG]
    negate: Optional[bool]
    z3_constraints: Dict[int, List[ExprRef]]
    is_feasible: bool

    def __init__(
        self,
        source: CFGBlock,
        target: CFGBlock,
        edge_label: Optional[str] = None,
        condition: Optional[NodeNG] = None,
        negate: Optional[bool] = None,
    ) -> None:
        self.source = source
        self.target = target
        self.label = edge_label
        self.condition = condition
        self.negate = negate
        self.source.successors.append(self)
        self.target.predecessors.append(self)
        self.z3_constraints = {}
        self.is_feasible = True

    def get_label(self) -> Optional[str]:
        """Return the edge label if specified.
        If `edge.label` is None, return the edge condition determined by the negation of `edge.negate`.
        Return None if both `edge.label` and `edge.negate` are None.
        """
        if self.label is not None:
            return self.label
        elif self.negate is not None:
            return str(not self.negate)
        return None


class Z3Environment:
    """Z3 Environment stores the Z3 variables and constraints in the current CFG path

    variable_unassigned:
        A dictionary mapping each variable in the current environment to a boolean indicating
        whether it has been reassigned (False) or remains unassigned (True).

    variables:
        A dictionary mapping each variable in the current environment to its z3 variable.

    constraints:
        A list of Z3 constraints in the current environment.
    """

    variable_unassigned: Dict[str, bool]
    variables: Dict[str, ExprRef]
    constraints: List[ExprRef]

    def __init__(self, variables: Dict[str, ExprRef], constraints: List[ExprRef]) -> None:
        """Initialize the environment with function parameters and preconditions"""
        self.variable_unassigned = {var: True for var in variables}
        self.variables = variables
        self.constraints = constraints.copy()

    def assign(self, name: str) -> None:
        """Handle a variable assignment statement"""
        if name in self.variable_unassigned:
            self.variable_unassigned[name] = False

    def update_constraints(self) -> List[ExprRef]:
        """Returns all z3 constraints in the environments
        Removes constraints with reassigned variables
        """
        updated_constraints = []
        for constraint in self.constraints:
            # discard expressions with reassigned variables
            variables = _get_vars(constraint)
            reassigned = any(
                not self.variable_unassigned.get(variable, False) for variable in variables
            )
            if not reassigned:
                updated_constraints.append(constraint)

        self.constraints = updated_constraints
        return updated_constraints.copy()

    def add_constraint(self, constraint: ExprRef) -> None:
        """Add a new z3 constraint to environment"""
        self.constraints.append(constraint)

    def parse_constraint(self, node: NodeNG) -> Optional[ExprRef]:
        """Parse an Astroid node to a Z3 constraint
        Return the resulting expression
        """
        parser = Z3Parser(self.variables)
        try:
            return parser.parse(node)
        except (Z3Exception, Z3ParseException):
            return None


def _get_vars(expr: ExprRef) -> Set[str]:
    """Retrieve all z3 variables from a z3 expression"""
    variables = set()

    def traverse(e: ExprRef) -> None:
        if is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED:
            variables.add(e.decl().name())
        elif hasattr(e, "children"):
            for child in e.children():
                traverse(child)

    traverse(expr)
    return variables
