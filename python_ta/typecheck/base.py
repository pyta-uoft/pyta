import sys
import typing
from itertools import product
from typing import *
from typing import IO  # Needed for type_store
from typing import Callable, ForwardRef, _GenericAlias, _type_check

from astroid import nodes

from python_ta.typecheck.errors import error_message
from python_ta.utils import _get_name, _gorg

from ..util.monad import Failable, failable_collect


class _TNode:
    """A node in the TypeConstraints disjoint set data structure."""

    type: type
    parent: Optional["_TNode"]
    parent_path: Optional[List[nodes.NodeNG]]
    adj_list: List[Tuple["_TNode", nodes.NodeNG]]
    ast_node: Optional[nodes.NodeNG]

    def __init__(self, node_type: type, ast_node: Optional[nodes.NodeNG] = None) -> None:
        self.type = node_type
        self.parent = None
        self.parent_path = None
        self.adj_list = []
        self.ast_node = ast_node

    def __eq__(self, other: "_TNode") -> bool:
        if str(self.type) == str(other.type):
            return True
        else:
            return False

    def __str__(self) -> str:
        if self.parent and self.ast_node:
            return f"TNode {self.ast_node.as_string()}: {self.type}, resolved to {self.parent.type}"
        elif self.ast_node:
            return f"TNode {self.ast_node.as_string()}: {self.type}"
        else:
            return f"TNode: {self.type}"

    def find_path_to_parent(self) -> List[nodes.NodeNG]:
        """Return list of astroid nodes relating _TNode to parent _TNode."""
        final_path = []
        cur_node = self
        while cur_node.parent_path:
            final_path.append(cur_node.parent_path[1])
            cur_node = cur_node.parent_path[0]
        return final_path

    def find_annotation(self) -> Optional[nodes.AnnAssign]:
        """Find annotation node in list of astroid nodes relating _TNode to parent _TNode, if one exists."""
        path = self.find_path_to_parent()
        for p in path:
            if isinstance(p, nodes.AnnAssign):
                return p


class TypeResult(Failable):
    """Represents the result of a type check operation that either succeeded or
    failed.
    """

    def __init__(self, value) -> None:
        super().__init__(value)


class TypeInfo(TypeResult):
    """Represents the result of a successful type check operation
    Contains information about the inferred type of a node
    """

    def __init__(self, type_: type) -> None:
        super().__init__(type_)

    def __repr__(self) -> str:
        return f"TypeInfo({repr(self.value)})"

    def __str__(self) -> str:
        return f"TypeInfo: {self.value}"


class NoType(TypeResult):
    """Class representing no inferred type"""

    def __init__(self) -> None:
        super().__init__(None)


class TypeFail(TypeResult):
    """Represents the result of a failed type check operation.
    Contains error message.
    """

    def __init__(self, msg: Optional[str] = None) -> None:
        self.msg = msg
        super().__init__(self.msg)

    def __str__(self) -> str:
        return f"TypeFail: {self.msg}"

    def bind(self, _) -> "TypeFail":
        return self


class TypeFailUnify(TypeFail):
    """
    TypeFailUnify occurs when two types fail to unify.

    :param tnodes: List of _TNodes that failed to unify. Usually contains two
    :param src_node: astroid node where failure occurs
    """

    def __init__(self, *tnodes: _TNode, src_node: nodes.NodeNG = None) -> None:
        self.tnodes = tnodes
        self.src_node = src_node
        super().__init__(str(self))

    def __str__(self) -> str:
        string = "TypeFail: Unable to Unify "
        string += (
            f"{self.tnodes[0].ast_node.as_string()}"
            if self.tnodes[0].ast_node
            else f"{self.tnodes[0].type}"
        )
        string += " <-> "
        string += (
            f"{self.tnodes[1].ast_node.as_string()}"
            if self.tnodes[1].ast_node
            else f"{self.tnodes[1].type}"
        )
        if self.src_node:
            string += f" at {self.src_node.as_string()}"
        return string


class TypeFailLookup(TypeFail):
    """
    TypeFailLookup occurs when an attribute variable or method is called, and either the attribute or
    class is invalid.

    :param class_tnode: _TNode of looked up class
    :param attr_node: astroid node representing looked up attribute
    :param src_node: astroid node where invalid lookup occurs
    """

    def __init__(
        self, class_tnode: _TNode, attr_node: nodes.NodeNG, src_node: nodes.NodeNG
    ) -> None:
        self.class_tnode = class_tnode
        self.attr_node = attr_node
        self.src_node = src_node
        super().__init__(str(self))

    def __str__(self) -> str:
        return f"TypeFail: Invalid attribute lookup {self.src_node.as_string()}"


class TypeFailAnnotationUnify(TypeFail):
    """
    TypeFailAnnotationUnify occurs when a contradiction occurs during the unification of the inferred type
    and the annotated type.

    :param tnode: _TNode of expected type
    :param src_node: astroid node where error occurs
    :param ann_node: astroid node where annotation is set
    """

    def __init__(
        self, tnode: _TNode, src_node: nodes.NodeNG = None, ann_node: nodes.NodeNG = None
    ) -> None:
        self.tnode = tnode
        self.src_node = src_node
        self.ann_node = ann_node
        super().__init__(str(self))

    def __str__(self) -> str:
        string = f"TypeFail: Annotation error in {self.src_node.as_string()}. {self.tnode.ast_node.as_string()} is annotated as "
        string += (
            f"{_get_name(self.tnode.parent.type)}"
            if self.tnode.parent
            else f"{_get_name(self.tnode.type)}"
        )
        string += f" at {self.ann_node.as_string()}"
        return string


class TypeFailAnnotationInvalid(TypeFail):
    """
    TypeFailAnnotationInvalid occurs when a variable is annotated as something other than a type

    :param src_node: astroid node where annotation is set
    """

    def __init__(self, src_node: nodes.NodeNG) -> None:
        self.src_node = src_node
        super().__init__(str(self))

    def __str__(self) -> str:
        return f"TypeFail: Annotation must be a type"


class TypeFailFunction(TypeFail):
    """
    TypeFailFunction occurs when a function is called with different arguments than expected.

    :param func_types: Tuple containing one or more acceptable type signatures
    :param funcdef_node: FunctionDef astroid node where function is defined
    :param src_node: Astroid node where invalid function call occurs
    :param arg_indices: List of argument index numbers,
    """

    def __init__(
        self,
        func_types: Tuple[Callable],
        funcdef_node: nodes.FunctionDef,
        src_node: nodes.NodeNG,
        arg_indices: List[int] = None,
    ) -> None:
        self.func_types = func_types
        self.funcdef_node = funcdef_node
        self.src_node = src_node
        self.arg_indices = arg_indices
        super().__init__(str(self))

    def __str__(self):
        return error_message(self)


class TypeFailReturn(TypeFail):
    """
    TypeFailReturn occurs when a nodes.Return node is encountered outside of a function definition.

    :param src_node: Invalid nodes.Return node
    """

    def __init__(self, src_node: nodes.Return) -> None:
        self.src_node = src_node
        super().__init__(str(self))

    def __str__(self) -> str:
        return f"TypeFail: Return statement not in valid function"


class TypeFailStarred(TypeFail):
    """
    TypeFailStarred occurs when there are multiple starred variables in the target of an assignment.

    :param src_node: Invalid nodes.Assign node
    """

    def __init__(self, src_node: nodes.Assign) -> None:
        self.src_node = src_node
        super().__init__(str(self))

    def __str__(self) -> str:
        return f"TypeFail: Multiple starred variables not valid"


def accept_failable(f: Callable) -> Callable:
    """Decorator to allow function fo to optionally acceptance instances of Failable as arguments."""

    def _f(*args, **kwargs):
        """Extract value from Failable arguments, pass values to function f.
        Return TypeFail instead if found.
        """
        new_args = []
        new_kwargs = {}
        for a in args:
            if isinstance(a, Failable):
                if isinstance(a, TypeFail):
                    return a
                a >> new_args.append
            else:
                new_args.append(a)
        for kw in kwargs:
            if isinstance(kwargs[kw], Failable):
                if isinstance(kwargs[kw], Failable):
                    return kwargs[kw]
                new_kwargs += kwargs[kw] >> (lambda t: dict(kw=t))
            else:
                new_kwargs[kw] = kwargs[kw]
        return f(*new_args, **new_kwargs)

    return _f


@accept_failable
def _wrap_generic_meta(t: _GenericAlias, args: List[type]) -> TypeResult:
    if t.__origin__ is tuple:
        tuple_args = tuple(args)
        # Handle the special case when t1 or t2 are empty tuples; TODO: investigate this
        if tuple_args == ((),):
            tuple_args = ()
        return TypeInfo(Tuple[tuple_args])
    elif is_callable(t):
        c = Callable.copy_with(tuple(args))
        c.__polymorphic_tvars__ = getattr(t, "__polymorphic_tvars__", frozenset())
        return TypeInfo(c)
    else:
        return TypeInfo(t.copy_with(tuple(args)))


@accept_failable
def wrap_container(container_type: _GenericAlias, *args: type) -> TypeResult:
    """Return instance of type container_type with type variable arguments args, wrapped in instance of TypeInfo."""
    return TypeInfo(container_type.copy_with(args))


Num = TypeVar("number", int, float)
a = TypeVar("a")
MulNum = TypeVar("mul_n", int, float, str, List[a])
tup1 = TypeVar("tup1")
tup2 = TypeVar("tup2")


class TuplePlus(TypeVar, _root=True):
    def eval_type(self, type_constraints: "TypeConstraints") -> TypeResult:
        t1, t2 = self.__constraints__
        t1 = type_constraints.resolve(t1).__params__
        t2 = type_constraints.resolve(t2).__params__
        return wrap_container(Tuple, t1, t2)


_TYPESHED_TVARS = {
    "_T": TypeVar("_T"),
    "_T_co": TypeVar("_T_co", covariant=True),
    "_KT": TypeVar("_KT"),
    "_VT": TypeVar("_VT"),
    "_S": TypeVar("_S"),
    "_T1": TypeVar("_T1"),
    "_T2": TypeVar("_T2"),
    "_T3": TypeVar("_T3"),
    "_T4": TypeVar("_T4"),
    "_T5": TypeVar("_T5"),
    "_TT": TypeVar("_TT", bound="type"),
    "function": Callable[[Any], Any],
}


_BUILTIN_TO_TYPING = {
    "list": "List",
    "dict": "Dict",
    "tuple": "Tuple",
    "set": "Set",
    "frozenset": "FrozenSet",
    "function": "Callable",
    "Iterator": "Iterator",
}


def _get_poly_vars(t: type) -> Set[str]:
    """Return a set consisting of the names of all TypeVars within t"""
    if isinstance(t, TypeVar) and t.__name__ in _TYPESHED_TVARS:
        return set([t.__name__])
    elif isinstance(t, _GenericAlias) and t.__args__:
        pvars = set()
        for arg in t.__args__:
            pvars.update(_get_poly_vars(arg))
        return pvars
    return set()


def create_Callable(
    args: Iterable[type], rtype: type, class_poly_vars: Set[type] = None
) -> Callable:
    """Initialize and return Callable with given parameters, return types, and polymorphic type variables."""
    poly_vars = set(class_poly_vars) if class_poly_vars else set()
    c = Callable.copy_with(tuple([*args, rtype]))
    poly_vars.update(_get_poly_vars(c))
    c.__polymorphic_tvars__ = frozenset(poly_vars)
    return c


@accept_failable
def create_Callable_TypeResult(
    args: Iterable[type], rtype: type, poly_vars: Set[type] = None
) -> TypeResult:
    """Return Callable wrapped in a TypeInfo instance."""
    return TypeInfo(create_Callable(args, rtype, poly_vars))


TYPE_SIGNATURES = {
    int: {
        "__add__": create_Callable([int, Num], Num, {Num}),
        "__sub__": create_Callable([int, Num], Num, {Num}),
        "__mul__": create_Callable([int, MulNum], MulNum, {MulNum}),
        "__idiv__": create_Callable([int, Num], Num, {Num}),
        "__mod__": create_Callable([int, Num], Num, {Num}),
        "__pow__": create_Callable([int, Num], Num, {Num}),
        "__div__": create_Callable([int, Num], float, {Num}),
    },
    float: {
        "__add__": create_Callable([float, Num], float, {Num}),
        "__sub__": create_Callable([float, Num], float, {Num}),
        "__mul__": create_Callable([float, Num], float, {Num}),
        "__idiv__": create_Callable([float, Num], float, {Num}),
        "__mod__": create_Callable([float, Num], float, {Num}),
        "__pow__": create_Callable([float, Num], float, {Num}),
        "__div__": create_Callable([float, Num], float, {Num}),
    },
    str: {"__add__": Callable[[str, str], str], "__mul__": Callable[[str, int], str]},
    List: {
        "__add__": create_Callable([List[a], List[a]], List[a], {a}),
        "__mul__": create_Callable([List[a], int], List[a], {a}),
        "__getitem__": create_Callable([List[a], int], a, {a}),
    },
    Tuple: {"__add__": create_Callable([tup1, tup2], TuplePlus("tup+", tup1, tup2), {tup1, tup2})},
}


def op_to_dunder_binary(op: str) -> str:
    """Return the dunder method name corresponding to binary op."""
    if op == "+":
        return "__add__"
    elif op == "-":
        return "__sub__"
    elif op == "*":
        return "__mul__"
    elif op == "//":
        return "__idiv__"
    elif op == "%":
        return "__mod__"
    elif op == "/":
        return "__div__"
    elif op == "**":
        return "__pow__"
    elif op == "&":
        return "__and__"
    elif op == "^":
        return "__xor__"
    elif op == "|":
        return "__or__"
    elif op == "==":
        return "__eq__"
    elif op == "!=":
        return "__ne__"
    elif op == "<":
        return "__lt__"
    elif op == "<=":
        return "__le__"
    elif op == ">":
        return "__gt__"
    elif op == ">=":
        return "__ge__"
    # TODO: 'is' and 'in'
    else:
        return op


def op_to_dunder_unary(op: str) -> str:
    """Return the dunder method name corresponding to unary op."""
    if op == "-":
        return "__neg__"
    elif op == "+":
        return "__pos__"
    elif op == "~":
        return "__invert__"
    else:
        return op


class TypeConstraints:
    """Represents all the type constraints in the program.

    This is mainly comprised of a disjoint set data structure, in which each disjoint set
    represents a set of equivalences of type variables and concrete types. The nodes
    in the disjoint set are implemented by the private class _TNode above.
    """

    # The number of type variables stored in the data structure. Used to generate fresh type variables.
    _count: int
    # List of _TNodes
    _nodes: List[_TNode]
    # A mapping of types to nodes
    type_to_tnode: Dict[str, _TNode]

    def __init__(self) -> None:
        self.type_store = None
        self.reset()

    def __deepcopy__(self, memodict: Dict = {}) -> "TypeConstraints":
        tc = TypeConstraints()
        tc._count = self._count
        tc._nodes = []
        tc.type_to_tnode = {}
        tc.type_store = self.type_store
        # copy nodes without copying edges
        for node in self._nodes:
            node_cpy = _TNode(node.type, node.ast_node)
            tc._nodes.append(node_cpy)
            tc.type_to_tnode[str(node.type)] = node_cpy
        # fill in edges
        for node in self._nodes:
            for adj_node, ctx in node.adj_list:
                tc.type_to_tnode[str(node.type)].adj_list.append(
                    (tc.type_to_tnode[str(adj_node.type)], ctx)
                )
            if node.parent:
                tc.type_to_tnode[str(node.type)].parent = tc.type_to_tnode[str(node.parent.type)]
        return tc

    def reset(self) -> None:
        """Reset the type constraints kept track of in the program."""
        self._count = 0
        self._nodes = []
        self.type_to_tnode = {}

    ###########################################################################
    # Creating new nodes ("make set")
    ###########################################################################
    # TODO: Rename to better distinguish between _TNodes and AST Nodes
    def fresh_tvar(self, node: Optional[nodes.NodeNG] = None) -> TypeVar:
        """Create and return a fresh type variable, associated with the given node."""
        tvar = TypeVar(f"_TV{self._count}")
        self._count += 1
        self._make_set(tvar, ast_node=node)
        return tvar

    def _make_set(self, t: type, ast_node: Optional[nodes.NodeNG] = None) -> _TNode:
        """Create new set with a single _TNode."""
        node = _TNode(t, ast_node)
        self._nodes.append(node)
        self.type_to_tnode[str(t)] = node
        if not isinstance(t, TypeVar):
            node.parent = node
        return node

    def get_tnode(self, t: type) -> _TNode:
        """Return the _TNode that represents the given type t, or create a new one."""
        try:
            node = self.type_to_tnode[str(t)]
        except KeyError:
            node = self._make_set(t, None)
        return node

    ###########################################################################
    # Type lookup ("find")
    ###########################################################################
    @accept_failable
    def resolve(self, t: type) -> TypeResult:
        """Return the concrete type or set representative associated with the given type."""
        if isinstance(t, _GenericAlias):
            if t.__args__ is not None:
                res_args = [self.resolve(arg) for arg in t.__args__]
                return _wrap_generic_meta(t, failable_collect(res_args))
            else:
                return TypeInfo(t)
        elif isinstance(t, TypeVar):
            try:
                repr = self.find_repr(self.type_to_tnode[str(t)])
                if repr and repr.type is not t:
                    if any(elt is t for elt in getattr(repr.type, "__args__", [])):
                        return TypeInfo(t)
                    else:
                        return self.resolve(repr.type)
            except KeyError:
                return TypeInfo(t)
        return TypeInfo(t)

    def is_concrete(self, t: type) -> bool:
        if isinstance(t, _GenericAlias):
            return all([self.is_concrete(arg) for arg in t.__args__])
        else:
            return not isinstance(t, TypeVar)

    def find_repr(self, tn: _TNode) -> Optional[_TNode]:
        """Search, using BFS starting from this _TNode, to find a _TNode that has a parent,
        or a unique set representative if no parent is found."""
        return self.find_parent(tn, True)

    def find_parent(self, tn: _TNode, find_repr: bool = False) -> Optional[_TNode]:
        """Search, using BFS starting from this _TNode, to find a _TNode that has a parent."""
        if tn.parent is not None:
            return tn.parent

        goal_tnode = self.find_node(tn, (lambda t: t.parent is not None), find_repr)

        if goal_tnode and goal_tnode.parent:
            cur_node = goal_tnode
            while cur_node:
                next_node = None
                for e in cur_node.adj_list:
                    if not e[0].parent_path and not e[0].parent:
                        e[0].parent = goal_tnode
                        e[0].parent_path = (cur_node, e[1])
                        next_node = e[0]
                cur_node = next_node

        return goal_tnode

    def find_function_def(self, tn: _TNode) -> Optional[nodes.FunctionDef]:
        """Search, using BFS starting from this _TNode, to find a _TNode with a
        FunctionDef node as its ast_node attribute."""
        func_tnode = self.find_node(
            tn, (lambda t: isinstance(t.ast_node, nodes.FunctionDef)), False
        )
        if func_tnode:
            return func_tnode.ast_node

    def find_node(
        self, tn: _TNode, cond: Callable[[Any], bool], find_repr: bool = False
    ) -> Optional[_TNode]:
        """Search, using BFS starting from this _TNode, to find a _TNode that satisfied passed in condition function."""
        visited = []
        node_list = [tn]
        goal_tnode = None
        while node_list:
            cur_node = node_list[0]
            for e in cur_node.adj_list:
                if e[0] not in visited and e[0] not in node_list:
                    if cond(e[0]):
                        goal_tnode = e[0]
                        break
                    node_list.append(e[0])
            visited.append(node_list[0])
            node_list.remove(node_list[0])

        # Return a set representative, even if it isn't a concrete type
        if find_repr and not goal_tnode and len(visited) > 1:
            visited_types = list(tnode.type for tnode in visited)
            visited_types.sort(key=(lambda t: t.__name__))
            goal_tnode = self.get_tnode(visited_types[-1])

        return goal_tnode

    def create_edges(self, tn1: _TNode, tn2: _TNode, ast_node: nodes.NodeNG):
        if tn1 != tn2:
            edge_exists = False
            for e in tn1.adj_list:
                if e[0] == tn2:
                    edge_exists = True
            if not edge_exists:
                tn1.adj_list.append((tn2, ast_node))
                tn2.adj_list.append((tn1, ast_node))

    ###########################################################################
    # Type unification ("union")
    ###########################################################################
    @accept_failable
    def unify(self, t1: type, t2: type, ast_node: Optional[nodes.NodeNG] = None) -> TypeResult:
        """Attempt to unify two types.

        :param t1: The first of the two types to be unified.
        :param t2: The second of the two types to be unified.
        :param ast_node: The astroid node responsible for the unification of t1 & t2.
        :returns: A TypeResult object (TypeFail or TypeInfo) containing information
            about the success / failure of the type unification.
        """

        # Get associated TNodes
        tnode1 = self.get_tnode(t1)
        tnode2 = self.get_tnode(t2)

        # Attempt to resolve to a TNode with concrete type
        conc_tnode1 = self.find_parent(tnode1)
        conc_tnode2 = self.find_parent(tnode2)

        # Both types can be resolved
        if conc_tnode1 is not None and conc_tnode2 is not None:
            ct1 = conc_tnode1.type
            ct2 = conc_tnode2.type
            if ct1 == ct2:
                tnode1.parent = conc_tnode1
                tnode2.parent = conc_tnode1
                self.create_edges(tnode1, tnode2, ast_node)
                return TypeInfo(ct1)
            elif (
                getattr(ct1, "__origin__", None) is Union
                or getattr(ct2, "__origin__", None) is Union
            ):
                ct1_types = ct1.__args__ if getattr(ct1, "__origin__", None) is Union else [ct1]
                ct2_types = ct2.__args__ if getattr(ct2, "__origin__", None) is Union else [ct2]
                for u1, u2 in product(ct1_types, ct2_types):
                    if self.can_unify(u1, u2):
                        return self.unify(u1, u2, ast_node)
                return TypeFailUnify(tnode1, tnode2, src_node=ast_node)
            elif isinstance(ct1, _GenericAlias) and isinstance(ct2, _GenericAlias):
                return self._unify_generic(tnode1, tnode2, ast_node)

            elif ct1 == Any or ct2 == Any:
                return TypeInfo(ct1) if ct1 != Any else TypeInfo(ct2)
            # Handle inheritance
            elif (
                self.type_store
                and ct1 is not None
                and ct2 is not None
                and self.type_store.is_descendant(ct1, ct2)
            ):
                return TypeInfo(ct1)
            else:
                for tn in [tnode1, tnode2]:
                    ann_t = tn.find_annotation()
                    if ann_t is not None:
                        return TypeFailAnnotationUnify(tn, ast_node, ann_t)
                return TypeFailUnify(tnode1, tnode2, src_node=ast_node)

        # One type can be resolved
        elif conc_tnode1 is not None:
            tnode2.parent = conc_tnode1
            tnode2.parent_path = (tnode1, ast_node)
            self.create_edges(tnode1, tnode2, ast_node)
            return TypeInfo(conc_tnode1.type)
        elif conc_tnode2 is not None:
            return self.unify(t2, t1, ast_node)

        # Both types are type variables
        elif t1 == t2:
            return TypeInfo(t1)
        else:
            self.create_edges(tnode1, tnode2, ast_node)
            return NoType()

    def _unify_generic(
        self, tnode1: _TNode, tnode2: _TNode, ast_node: Optional[nodes.NodeNG] = None
    ) -> TypeResult:
        """Unify two generic types (e.g., List, Tuple, Dict, Callable)."""

        conc_tnode1 = self.find_parent(tnode1)
        conc_tnode2 = self.find_parent(tnode2)

        g1, g2 = _gorg(conc_tnode1.type), _gorg(conc_tnode2.type)
        if not self.type_store or not self.type_store.is_descendant(
            conc_tnode1.type, conc_tnode2.type
        ):
            if (
                g1 is not g2
                or conc_tnode1.type.__args__ is None
                or conc_tnode2.type.__args__ is None
            ):
                # TODO: need to store more info here and in the case below
                return TypeFailUnify(conc_tnode1, conc_tnode2, src_node=ast_node)
            if len(conc_tnode1.type.__args__) != len(conc_tnode2.type.__args__):
                return TypeFailUnify(conc_tnode1, conc_tnode2, src_node=ast_node)

        arg_inf_types = []
        for a1, a2 in zip(conc_tnode1.type.__args__, conc_tnode2.type.__args__):
            if a1 == () or a2 == ():
                result = TypeInfo(())
            else:
                result = self.unify(a1, a2, ast_node)

            if isinstance(result, TypeFail):
                arg_inf_types = [TypeFailUnify(tnode1, tnode2, src_node=ast_node)]
                break
            else:
                arg_inf_types.append(result)

        unified_args = failable_collect(arg_inf_types)

        result = _wrap_generic_meta(conc_tnode1.type, unified_args)
        if not isinstance(result, TypeFail):
            self.create_edges(tnode1, tnode2, ast_node)
        return result

    ###########################################################################
    # Handling generic polymorphism
    ###########################################################################
    def can_unify(self, t1: type, t2: type) -> bool:
        """Check if the two types can unify without modifying current TypeConstraints."""
        tc = self.__deepcopy__()
        return not isinstance(tc.unify(t1, t2, None), TypeFail)

    @accept_failable
    def unify_call(
        self, func_var: type, *arg_types: type, node: Optional[nodes.NodeNG] = None
    ) -> TypeResult:
        """Unify a function call with the given function type and argument types.

        Return a result type.
        """
        if is_callable(func_var):
            func_type = func_var
        else:
            func_var_tnode = self.get_tnode(func_var)
            parent_tnode = self.find_parent(func_var_tnode)
            func_type = parent_tnode.type

        # Check for Callable[..., T]
        if is_callable(func_type) and func_type.__args__[0] is ...:
            return TypeInfo(func_type.__args__[-1])

        # Check that the number of parameters matches the number of arguments.
        if func_type.__origin__ is Union:
            new_func_type = None
            for c in func_type.__args__:
                if len(c.__args__) - 1 == len(arg_types):
                    new_func_type = c
                    break
            if new_func_type is None:
                func_var_tnode = self.get_tnode(func_var)
                funcdef_node = self.find_function_def(func_var_tnode)
                return TypeFailFunction(tuple(func_type.__args__), funcdef_node, node)
            else:
                func_type = new_func_type
        elif len(func_type.__args__) - 1 != len(arg_types):
            func_var_tnode = self.get_tnode(func_var)
            funcdef_node = self.find_function_def(func_var_tnode)
            return TypeFailFunction((func_type,), funcdef_node, node)
        new_func_type = self.fresh_callable(func_type, node)
        func_params = getattr(new_func_type, "__args__", [None])[:-1]
        arg_types = list(arg_types)
        for param, i in zip(func_params, range(len(arg_types))):
            # Automatic conversion of iterable types to Iterable[T]
            if isinstance(param, _GenericAlias) and param.__origin__ is Iterable.__origin__:
                arg = self.resolve(arg_types[i])
                func_type = self.type_store.lookup_method("__iter__", arg.getValue(), node=node)

                if isinstance(func_type, TypeFail):
                    func_var_tnode = self.get_tnode(func_var)
                    funcdef_node = self.find_function_def(func_var_tnode)
                    return TypeFailFunction((func_type,), funcdef_node, node)

                iterator_type = self.unify_call(func_type, arg_types[i], node=node)
                if isinstance(iterator_type, TypeFail):
                    func_var_tnode = self.get_tnode(func_var)
                    funcdef_node = self.find_function_def(func_var_tnode)
                    return TypeFailFunction((func_type,), funcdef_node, node)

                arg_types[i] = Iterable[iterator_type.getValue().__args__[0]]

        results = []
        for i in range(len(arg_types)):
            result = self.unify(arg_types[i], new_func_type.__args__[i], node)
            if isinstance(result, TypeFail):
                func_var_tnode = self.get_tnode(func_var)
                funcdef_node = self.find_function_def(func_var_tnode)
                param_annotations = funcdef_node.args.annotations if funcdef_node else None
                if param_annotations and param_annotations[i] is not None:
                    tvar = funcdef_node.type_environment.lookup_in_env(
                        funcdef_node.args.args[i].name
                    )
                    tnode = self.get_tnode(tvar)
                    return TypeFailAnnotationUnify(tnode, node, funcdef_node)
                else:
                    results.append(i)
        if results:
            func_var_tnode = self.get_tnode(func_var)
            funcdef_node = self.find_function_def(func_var_tnode)
            return TypeFailFunction((new_func_type,), funcdef_node, node, results)
        return self._type_eval(new_func_type.__args__[-1])

    def _type_eval(self, t: type) -> TypeResult:
        """Evaluate a type. Used for tuples."""
        if isinstance(t, TuplePlus):
            return t.eval_type(self)
        if isinstance(t, TypeVar):
            return self.resolve(t)
        if isinstance(t, _GenericAlias) and t.__args__ is not None:
            inf_args = (self._type_eval(argument) for argument in t.__args__)
            return wrap_container(t, *inf_args)
        else:
            return TypeInfo(t)

    def fresh_callable(self, func_type: type, node: Optional[nodes.NodeNG]) -> type:
        """Given a callable, substitute all polymorphic variables with fresh ones"""
        new_tvars = {
            tvar: self.fresh_tvar(node) for tvar in getattr(func_type, "__polymorphic_tvars__", [])
        }
        return literal_substitute(func_type, new_tvars)


def literal_substitute(t: type, type_map: Dict[str, type]) -> type:
    """Make substitutions in t according to type_map, returning resulting type."""
    if isinstance(t, TypeVar) and t.__name__ in type_map:
        return type_map[t.__name__]
    elif isinstance(t, TypeVar):
        return TypeVar(t.__name__)
    elif isinstance(t, ForwardRef):
        return ForwardRef(literal_substitute(t.__forward_arg__, type_map))
    elif isinstance(t, TuplePlus):
        subbed_args = [literal_substitute(t1, type_map) for t1 in t.__constraints__]
        return TuplePlus("tup+", *subbed_args)
    elif is_callable(t):
        args = list(literal_substitute(t1, type_map) for t1 in t.__args__[:-1])
        res = literal_substitute(t.__args__[-1], type_map)
        new_t = Callable[args, res]
        if hasattr(t, "__polymorphic_tvars__"):
            new_t.__polymorphic_tvars__ = t.__polymorphic_tvars__.copy()
        return new_t
    elif isinstance(t, _GenericAlias) and t.__args__ is not None:
        return t.copy_with(tuple(literal_substitute(t1, type_map) for t1 in t.__args__))
    else:
        return t


class Environment:
    """The type bindings for the environment for a particular node.

    Instances of this class contain three dictionaries, representing bindings
    for local, nonlocal, and global bindings.

    TODO: currently, only locals is used; this should be fixed as we add
    the nonlocal and global nodes and use scope information to categorize
    a name binding.
    """

    def __init__(
        self,
        locals_: Optional[Dict[str, type]] = None,
        nonlocals_: Optional[Dict[str, type]] = None,
        globals_: Optional[Dict[str, type]] = None,
    ) -> None:
        """Initialize an environment."""
        self.locals = locals_ or {}
        self.nonlocals = nonlocals_ or {}
        self.globals = globals_ or {}

    def lookup_in_env(self, variable_name: str) -> type:
        """Helper to search for a variable in the environment of a node by name."""
        if variable_name in self.locals:
            return self.locals[variable_name]
        elif variable_name in self.globals:
            return self.globals[variable_name]
        elif variable_name in self.nonlocals:
            return self.nonlocals[variable_name]
        else:
            raise KeyError

    def create_in_env(
        self,
        type_constraints: TypeConstraints,
        environment: "Environment",
        variable_name: str,
        node: nodes.NodeNG,
    ):
        """Helper to create a fresh Type Var and adding the variable to appropriate environment."""
        if environment == "locals":
            self.locals[variable_name] = type_constraints.fresh_tvar(node)
        elif environment == "globals":
            self.globals[variable_name] = type_constraints.fresh_tvar(node)
        elif environment == "nonlocals":
            self.nonlocals[variable_name] = type_constraints.fresh_tvar(node)

    def __str__(self) -> str:
        return str(self.locals)


###############################################################################
# Parsing type annotations
###############################################################################
def parse_annotations(
    node: nodes.NodeNG, class_tvars: Optional[List[type]] = None
) -> List[Tuple[type, str]]:
    """Return types specified by the type annotations for a node.
    Returns more than one type if there are default arguments.
    """
    if isinstance(node, nodes.FunctionDef):
        arg_types = []
        no_class_tvars = class_tvars is None
        is_methodcall = isinstance(node.parent, nodes.ClassDef)
        if no_class_tvars and is_methodcall:
            self_type = _node_to_type(node.parent.name)
        elif no_class_tvars or not is_methodcall:
            self_type = None
        elif node.parent.name in _BUILTIN_TO_TYPING:
            self_type = eval(_BUILTIN_TO_TYPING[node.parent.name])[
                tuple(_node_to_type(tv) for tv in class_tvars)
            ]
        else:
            self_type = _node_to_type(node.parent.name)

        for arg, annotation in zip(node.args.args, node.args.annotations):
            if getattr(arg, "name", None) == "self" and annotation is None:
                arg_types.append(self_type)
            else:
                arg_types.append(_ann_node_to_type(annotation).getValue())

        # Handle optional arguments
        alternatives = []
        for num_optional in range(len(node.args.defaults) + 1):
            alternatives.append(arg_types[: len(arg_types) - num_optional])

        rtype = _ann_node_to_type(node.returns).getValue()

        callables = [
            (create_Callable(arg_types, rtype, class_tvars), node.type)
            for arg_types in alternatives
        ]
        return callables

    elif isinstance(node, nodes.AssignName) and isinstance(node.parent, nodes.AnnAssign):
        return [_ann_node_to_type(node.parent.annotation).getValue(), "attribute"]


def _ann_node_to_type(node: nodes.Name) -> TypeResult:
    """Return a type represented by the input node, substituting Any for missing arguments in generic types"""
    try:
        ann_node_type = _node_to_type(node)
    except SyntaxError:
        # Attempted to create ForwardRef with invalid string
        return TypeFailAnnotationInvalid(node)

    ann_type = _generic_to_annotation(ann_node_type, node)
    return ann_type


def _generic_to_annotation(ann_node_type: type, node: nodes.NodeNG) -> TypeResult:
    is_generic = isinstance(ann_node_type, _GenericAlias) or (
        sys.version_info >= (3, 9) and hasattr(ann_node_type, "__origin__")
    )
    if is_generic and ann_node_type is getattr(
        typing, getattr(ann_node_type, "_name", "") or "", None
    ):
        if ann_node_type == Dict:
            ann_type = wrap_container(ann_node_type, Any, Any)
        elif ann_node_type == Tuple:
            # TODO: Add proper support for multi-parameter Tuples
            ann_type = wrap_container(ann_node_type, Any)
        else:
            ann_type = wrap_container(ann_node_type, Any)
    elif is_generic:
        parsed_args = []
        for arg in ann_node_type.__args__:
            _generic_to_annotation(arg, node) >> parsed_args.append
        ann_type = wrap_container(ann_node_type, *parsed_args)
    else:
        try:
            _type_check(ann_node_type, "")
        except TypeError:
            return TypeFailAnnotationInvalid(node)
        else:
            ann_type = TypeInfo(ann_node_type)
    return ann_type


def _node_to_type(node: nodes.NodeNG, locals: Dict[str, type] = None) -> type:
    """Return a type represented by the input node."""
    locals = locals or _TYPESHED_TVARS
    if node is None:
        return Any
    elif isinstance(node, str):
        return _eval_node(node, globals(), locals)
    elif isinstance(node, nodes.Name):
        return _eval_node(node.name, globals(), locals)
    elif isinstance(node, nodes.Attribute):
        return _eval_node(node.attrname, globals(), locals)
    elif isinstance(node, nodes.Subscript):
        v = _node_to_type(node.value)
        s = _node_to_type(node.slice)
        if isinstance(v, ForwardRef):
            return literal_substitute(v, {v.__forward_arg__: s})
        else:
            return v[s]
    elif isinstance(node, nodes.Index):
        return _node_to_type(node.value)
    elif isinstance(node, nodes.Tuple):
        return tuple(_node_to_type(t) for t in node.elts if not isinstance(t, nodes.Ellipsis))
    elif isinstance(node, nodes.List):
        return [_node_to_type(t) for t in node.elts if not isinstance(t, nodes.Ellipsis)]
    elif isinstance(node, nodes.Const) and node.value is None:
        return None
    elif isinstance(node, nodes.Const) and isinstance(node.value, str):
        return _node_to_type(node.value)
    elif isinstance(node, nodes.Const) and node.value is Ellipsis:
        return Ellipsis
    else:
        return node


def _eval_node(node_name: str, _globals: Dict[str, type], _locals: Dict[str, type]):
    """Return a type represented by node_name."""
    try:
        eval_type = eval(node_name, _globals, _locals)
    except:
        eval_type = ForwardRef(node_name)

    if eval_type in (list, dict, tuple, set):
        # Annotation set as class type (ie. list) instead of typing generic (ie. List[Any])
        return eval(f"typing.{node_name.capitalize()}", _globals, _locals)
    else:
        return eval_type


def _collect_tvars(type: type) -> List[type]:
    if isinstance(type, TypeVar):
        return [type]
    elif isinstance(type, _GenericAlias) and type.__args__:
        return sum([_collect_tvars(arg) for arg in type.__args__], [])
    else:
        return []


def class_callable(init: Callable) -> Callable:
    """Convert an __init__ type signature into a callable for the class."""
    c = init.copy_with(tuple([*init.__args__[1:-1], init.__args__[0]]))
    c.__polymorphic_tvars__ = init.__polymorphic_tvars__.copy()
    return c


def is_callable(t: type) -> bool:
    """Return whether the given type is a typing.Callable type."""
    return getattr(t, "__origin__", None) is Callable.__origin__
