import sys
from typing import *
from typing import CallableMeta, GenericMeta, TupleMeta, _ForwardRef, IO
import typing
import astroid
from astroid.node_classes import NodeNG
from itertools import product
from ..util.monad import Failable, failable_collect


class _TNode:
    """A node in the TypeConstraints disjoint set data structure."""
    type: type
    parent: Optional['_TNode']
    adj_list: List[Tuple['_TNode', NodeNG]]
    ast_node: Optional[NodeNG]

    def __init__(self, node_type: type, ast_node: Optional[NodeNG] = None):
        self.type = node_type
        self.parent = None
        self.parent_path = None
        self.adj_list = []
        self.ast_node = ast_node

    def __eq__(self, other: '_TNode') -> bool:
        if str(self.type) == str(other.type):
            return True
        else:
            return False

    def __str__(self) -> str:
        if self.parent and self.ast_node:
            return f'TNode {self.ast_node.as_string()}: {self.type}, resolved to {self.parent.type}'
        elif self.ast_node:
            return f'TNode {self.ast_node.as_string()}: {self.type}'
        else:
            return f'TNode: {self.type}'

    def find_path_to_parent(self) -> List[NodeNG]:
        """Finds path from the current node to its parent node, if one exists.
        Returns a list of astroid nodes, representing the chain of inferences that leads
        the current node to be resolved to its parent node
        """
        final_path = []
        cur_node = self
        while cur_node.parent_path:
            final_path.append(cur_node.parent_path[1])
            cur_node = cur_node.parent_path[0]
        return final_path

    def find_annotation(self) -> Optional[astroid.AnnAssign]:
        """Gets path from node to parent, and returns an AnnAssign (annotation) node if one exists in the path
        """
        # TODO: Add support for annotations within function definitions
        path = self.find_path_to_parent()
        for p in path:
            if isinstance(p, astroid.AnnAssign):
                return p


class TypeResult(Failable):
    """Represents the result of a type check operation that either succeeded or
    failed.
    """
    def __init__(self, value):
        super().__init__(value)


class TypeInfo(TypeResult):
    """Represents the result of a successful type check operation
    Contains information about the inferred type of a node
    """

    def __init__(self, type_: type):
        super().__init__(type_)

    def __str__(self) -> str:
        return f'TypeInfo: {self.value}'


class NoType(TypeResult):
    """Class representing no inferred type"""
    def __init__(self):
        super().__init__(None)


class TypeFail(TypeResult):
    """Represents the result of a failed type check operation
    Contains error message
    """
    def __init__(self, msg: Optional[str] = None):
        self.msg = msg
        super().__init__(self.msg)

    def __str__(self) -> str:
        return f'TypeFail: {self.msg}'

    def bind(self, _) -> 'TypeFail':
        return self


class TypeFailUnify(TypeFail):
    """
    TypeFailUnify occurs when two types fail to unify.
    Should be initialized with two valid _TNodes, and the astroid node where the failure occurred
    """
    def __init__(self, *tnodes: List[_TNode], src_node: NodeNG = None):
        self.tnodes = tnodes
        self.src_node = src_node
        super().__init__(str(self))

    def __str__(self) -> str:
        string = 'TypeFail: Unable to Unify '
        string += f'{self.tnodes[0].ast_node.as_string()}' if self.tnodes[0].ast_node else f'{self.tnodes[0].type}'
        string += ' <-> '
        string += f'{self.tnodes[1].ast_node.as_string()}' if self.tnodes[1].ast_node else f'{self.tnodes[1].type}'
        if self.src_node:
            string += f' at {self.src_node.as_string()}'
        return string


class TypeFailLookup(TypeFail):
    """
    TypeFailLookup occurs when an attribute variable or method is called, and either the attribute or
    class is invalid
    Should be initialized with the astroid function node where the invalid lookup occurred
    """
    def __init__(self, class_tnode: type, attr_node: NodeNG, src_node: NodeNG):
        self.class_tnode = class_tnode
        self.attr_node = attr_node
        self.src_node = src_node
        super().__init__(str(self))

    def __str__(self) -> str:
        return f'TypeFail: Invalid attribute lookup {self.src_node.as_string()}'


class TypeFailAnnotation(TypeFail):
    """
    TypeFailAnnotation occurs when a type is not used correctly, based on an inference from an annotated type
    Should be initialized with the _TNode of the expected type, the astroid node where the annotation occurs, and
    the astroid node where the error occurs
    """
    def __init__(self, tnode: _TNode, src_node: NodeNG = None, ann_node: NodeNG = None):
        self.tnode = tnode
        self.src_node = src_node
        self.ann_node = ann_node
        super().__init__(str(self))

    def __str__(self) -> str:
        string = f'TypeFail: Annotation error in {self.src_node.as_string()}. {self.tnode.ast_node.as_string()} is annotated as '
        string += f'{self.tnode.parent.type.__name__}' if self.tnode.parent else f'{self.tnode.type.__name__}'
        string += f' at {self.ann_node.as_string()}'
        return string


class TypeFailFunction(TypeFail):
    """
    TypeFailFunction occurs when a function is called with different arguments than expected.
    Should be initialized with the tnode of the expected function type signature, and astroid
    node where invalid function call occurred

    :param func_types: Tuple containing one or more valid type signatures
    :param funcdef_node: FunctionDef astroid node where function is defined
    :param src_node: Astroid node where invalid function call occurs
    :param arg_indices: List of argument index numbers,
    """
    def __init__(self, func_types: Tuple[CallableMeta], funcdef_node: astroid.FunctionDef, src_node: NodeNG,
                 arg_indices: List[int] = None):
        self.func_types = func_types
        self.funcdef_node = funcdef_node
        self.src_node = src_node
        self.arg_indices = arg_indices
        super().__init__(str(self))

    def __str__(self):
        return f'TypeFail: Invalid function call at {self.src_node.as_string()}'


# Make _gorg compatible for Python 3.6.2 and 3.6.3.
def _gorg(x):
    if sys.version_info < (3, 6, 3):
        return typing._gorg(x)
    else:
        return x._gorg


def accept_failable(f: Callable) -> Callable:
    """Wrapper that allows function f to optionally accept instances of type Failable as arguments.
    If an argument is an instance of Failable, the value is extracted and passed to function f.
    If any of the arguments are an instance of TypeFail, that instance is returned, and the function f is not called
    """
    def _f(*args, **kwargs):
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
def _wrap_generic_meta(t: GenericMeta, args: List[type]) -> TypeResult:
    if t == Tuple:
        tuple_args = tuple(args)
        # Handle the special case when t1 or t2 are empty tuples; TODO: investigate this
        if tuple_args == ((),):
            tuple_args = ()
        return TypeInfo(Tuple[tuple_args])
    elif t == Callable:
        return TypeInfo(Callable[args[:-1], args[-1]])
    else:
        return TypeInfo(t[tuple(args)])


@accept_failable
def wrap_container(container_type: GenericMeta, *args: List[type]) -> TypeResult:
    """
    Helper function, takes a list of types args and returns a generic of type container_type, with args as its elements
    """
    if isinstance(container_type, CallableMeta):
        return TypeInfo(Callable[list(args[:-1]), args[-1]])
    else:
        return TypeInfo(container_type[tuple(args)])


Num = TypeVar('number', int, float)
a = TypeVar('a')
MulNum = TypeVar('mul_n', int, float, str, List[a])
tup1 = TypeVar('tup1')
tup2 = TypeVar('tup2')


class TuplePlus(TypeVar, _root=True):
    def eval_type(self, type_constraints: 'TypeConstraints') -> TypeResult:
        t1, t2 = self.__constraints__
        t1 = type_constraints.resolve(t1).__params__
        t2 = type_constraints.resolve(t2).__params__
        return wrap_container(Tuple, t1, t2)


class TupleSubscript(TypeVar, _root=True):
    pass


_TYPESHED_TVARS = {
    '_T': TypeVar('_T'),
    '_T_co': TypeVar('_T_co', covariant=True),
    '_KT': TypeVar('_KT'),
    '_VT': TypeVar('_VT'),
    '_S': TypeVar('_S'),
    '_T1': TypeVar('_T1'),
    '_T2': TypeVar('_T2'),
    '_T3': TypeVar('_T3'),
    '_T4': TypeVar('_T4'),
    '_T5': TypeVar('_T5'),
    '_TT': TypeVar('_TT', bound='type'),
    'function': Callable[[Any], Any]
}


_BUILTIN_TO_TYPING = {
    'list': 'List',
    'dict': 'Dict',
    'tuple': 'Tuple',
    'set': 'Set',
    'frozenset': 'FrozenSet',
    'function': 'Callable'
}


def _get_poly_vars(t: type):
    if isinstance(t, TypeVar) and t.__name__ in _TYPESHED_TVARS:
        return set([t.__name__])
    elif isinstance(t, GenericMeta) and t.__args__:
        pvars = set()
        for arg in t.__args__:
            pvars.update(_get_poly_vars(arg))
        return pvars
    return set()


def create_Callable(args: Iterable[type], rtype: type, class_poly_vars=None) -> Callable:
    poly_vars = class_poly_vars or []
    poly_vars = set(poly_vars)
    c = Callable[list(args), rtype]
    poly_vars.update(_get_poly_vars(c))
    c.polymorphic_tvars = set()
    c.polymorphic_tvars.update(poly_vars)
    return c


@accept_failable
def create_Callable_TypeResult(args: Iterable[type], rtype: type, poly_vars=None) -> TypeResult:
    """Return Callable wrapped in a TypeInfo instance"""
    return TypeInfo(create_Callable(args, rtype, poly_vars))


TYPE_SIGNATURES = {
    int: {
        '__add__': create_Callable([int, Num], Num, {Num}),
        '__sub__': create_Callable([int, Num], Num, {Num}),
        '__mul__': create_Callable([int, MulNum], MulNum, {MulNum}),
        '__idiv__': create_Callable([int, Num], Num, {Num}),
        '__mod__': create_Callable([int, Num], Num, {Num}),
        '__pow__': create_Callable([int, Num], Num, {Num}),
        '__div__': create_Callable([int, Num], float, {Num}),
    },
    float: {
        '__add__': create_Callable([float, Num], float, {Num}),
        '__sub__': create_Callable([float, Num], float, {Num}),
        '__mul__': create_Callable([float, Num], float, {Num}),
        '__idiv__': create_Callable([float, Num], float, {Num}),
        '__mod__': create_Callable([float, Num], float, {Num}),
        '__pow__': create_Callable([float, Num], float, {Num}),
        '__div__': create_Callable([float, Num], float, {Num}),
    },
    str: {
        '__add__': Callable[[str, str], str],
        '__mul__': Callable[[str, int], str]
    },
    List: {
        '__add__': create_Callable([List[a], List[a]], List[a], {a}),
        '__mul__': create_Callable([List[a], int], List[a], {a}),
        '__getitem__': create_Callable([List[a], int], a, {a})
    },
    Tuple: {
        '__add__': create_Callable([tup1, tup2], TuplePlus('tup+', tup1, tup2), {tup1, tup2}),
    }
}


def op_to_dunder_binary(op: str) -> str:
    """Return the dunder method name corresponding to binary op."""
    if op == '+':
        return '__add__'
    elif op == '-':
        return '__sub__'
    elif op == '*':
        return '__mul__'
    elif op == '//':
        return '__idiv__'
    elif op == '%':
        return '__mod__'
    elif op == '/':
        return '__div__'
    elif op == '**':
        return '__pow__'
    elif op == '&':
        return '__and__'
    elif op == '^':
        return '__xor__'
    elif op == '|':
        return '__or__'
    elif op == '==':
        return '__eq__'
    elif op == '!=':
        return '__ne__'
    elif op == '<':
        return '__lt__'
    elif op == '<=':
        return '__le__'
    elif op == '>':
        return '__gt__'
    elif op == '>=':
        return '__ge__'
    # TODO: 'is' and 'in'
    else:
        return op


def op_to_dunder_unary(op: str) -> str:
    """Return the dunder method name corresponding to unary op."""
    if op == '-':
        return '__neg__'
    elif op == '+':
        return '__pos__'
    elif op == '~':
        return '__invert__'
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

    def __init__(self):
        self.type_store = None
        self.reset()

    def __deepcopy__(self, memodict={}):
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
                tc.type_to_tnode[str(node.type)].adj_list.append((tc.type_to_tnode[str(adj_node.type)], ctx))
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
    def fresh_tvar(self, node: Optional[NodeNG] = None) -> TypeVar:
        """Create and return a fresh type variable, associated with the given node.
        """
        tvar = TypeVar(f'_T{self._count}')
        self._count += 1
        self._make_set(tvar, ast_node=node)
        return tvar

    def _make_set(self, t: type, ast_node: Optional[NodeNG] = None) -> _TNode:
        """Creates new set with a single TNode"""
        node = _TNode(t, ast_node)
        self._nodes.append(node)
        self.type_to_tnode[str(t)] = node
        if not isinstance(t, TypeVar):
            node.parent = node
        return node

    def get_tnode(self, t: type) -> _TNode:
        """Returns the TNode that represents the given type t, or creates a new one"""
        try:
            node = self.type_to_tnode[str(t)]
        except KeyError:
            node = self._make_set(t, None)
        return node

    ###########################################################################
    # Type lookup ("find")
    ###########################################################################
    @accept_failable
    def resolve(self, t: type) -> TypeInfo:
        """Return the concrete type or set representative associated with the given type.
        """
        if isinstance(t, GenericMeta):
            res_args = [self.resolve(arg) for arg in t.__args__]
            return _wrap_generic_meta(_gorg(t), failable_collect(res_args))
        elif isinstance(t, TypeVar):
            try:
                repr = self.find_repr(self.type_to_tnode[str(t)])
                if repr and repr.type is not t:
                    return self.resolve(repr.type)
            except KeyError:
                return TypeInfo(t)
        return TypeInfo(t)

    def is_concrete(self, t: type):
        if isinstance(t, GenericMeta):
            return all([self.is_concrete(arg) for arg in t.__args__])
        else:
            return not isinstance(t, TypeVar)

    def find_repr(self, tn: _TNode) -> Optional[_TNode]:
        """Do a bfs starting from tn to find a _TNode that has a parent, or a unique set representative if
        no parent is found."""
        return self.find_parent(tn, True)

    def find_parent(self, tn: _TNode, find_repr: bool = False) -> Optional[_TNode]:
        """Do a bfs starting from tn to find a _TNode that has a parent."""
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

    def find_function_def(self, tn: _TNode) -> Optional[astroid.FunctionDef]:
        """Do a bfs starting from tn to find a _TNode with a FunctionDef node as its ast_node attribute."""
        func_tnode = self.find_node(tn, (lambda t: isinstance(t.ast_node, astroid.FunctionDef)), False)
        if func_tnode:
            return func_tnode.ast_node

    def find_node(self, tn: _TNode, cond: Callable[[Any], bool], find_repr: bool = False) -> Optional[_TNode]:
        """Do a bfs starting from tn to find a _TNode that satisfies the passed in condition function."""
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

    def create_edges(self, tn1: _TNode, tn2: _TNode, ast_node: NodeNG) -> None:
        """Create an edge between the two TNodes, if one does not already exist"""
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
    def unify(self, t1: type, t2: type,
              ast_node: Optional[NodeNG] = None) -> TypeResult:
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
            elif isinstance(ct1, GenericMeta) and isinstance(ct2, GenericMeta):
                return self._unify_generic(tnode1, tnode2, ast_node)
            elif ct1.__class__.__name__ == '_Union' or ct2.__class__.__name__ == '_Union':
                ct1_types = ct1.__args__ if ct1.__class__.__name__ == '_Union' else [ct1]
                ct2_types = ct2.__args__ if ct2.__class__.__name__ == '_Union' else [ct2]
                for u1, u2 in product(ct1_types, ct2_types):
                    if self.can_unify(u1, u2):
                        return self.unify(u1, u2, ast_node)
                return TypeFailUnify(tnode1, tnode2, src_node=ast_node)
            elif ct1 == Any or ct2 == Any:
                return TypeInfo(ct1)
            # Handle inheritance
            elif self.type_store and \
                    self.type_store.is_descendant(ct1, ct2):
                return TypeInfo(ct1)
            else:
                for tn in [tnode1, tnode2]:
                    ann_t = tn.find_annotation()
                    if ann_t is not None:
                        return TypeFailAnnotation(tn, ast_node, ann_t)
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

    def _unify_generic(self, tnode1: _TNode, tnode2: _TNode,
                       ast_node: Optional[NodeNG] = None) -> TypeResult:
        """Unify two generic types (e.g., List, Tuple, Dict, Callable)."""

        conc_tnode1 = self.find_parent(tnode1)
        conc_tnode2 = self.find_parent(tnode2)

        g1, g2 = _gorg(conc_tnode1.type), _gorg(conc_tnode2.type)
        if g1 is not g2 or conc_tnode1.type.__args__ is None or conc_tnode2.type.__args__ is None:
            # TODO: need to store more info here and in the case below
            return TypeFailUnify(conc_tnode1, conc_tnode2, src_node=ast_node)
        if len(conc_tnode1.type.__args__) != len(conc_tnode2.type.__args__):
            return TypeFailUnify(conc_tnode1, conc_tnode2, src_node=ast_node)

        arg_inf_types = []
        for a1, a2 in zip(conc_tnode1.type.__args__, conc_tnode2.type.__args__):
            result = self.unify(a1, a2, ast_node)
            if isinstance(result, TypeFail):
                arg_inf_types = [TypeFailUnify(tnode1, tnode2, src_node=ast_node)]
                break
            else:
                arg_inf_types.append(result)

        unified_args = failable_collect(arg_inf_types)

        self.create_edges(tnode1, tnode2, ast_node)
        return _wrap_generic_meta(g1, unified_args)

    ###########################################################################
    # Handling generic polymorphism
    ###########################################################################
    def can_unify(self, t1: type, t2: type) -> bool:
        """Check if the two types can unify without modifying current TypeConstraints."""
        tc = self.__deepcopy__()
        return isinstance(tc.unify(t1, t2, None), TypeInfo)

    @accept_failable
    def unify_call(self, func_var, *arg_types, node=None) -> TypeResult:
        """Unify a function call with the given function type and argument types.

        Return a result type.
        """
        if isinstance(func_var, CallableMeta):
            func_type = func_var
        else:
            tnode = self.get_tnode(func_var)
            func_tnode = self.find_parent(tnode)
            func_type = func_tnode.type

        # Check that the number of parameters matches the number of arguments.
        if func_type.__origin__ is Union:
            new_func_type = None
            for c in func_type.__args__:
                if len(c.__args__) - 1 == len(arg_types):
                    new_func_type = c
                    break
            if new_func_type is None:
                func_tnode = self.get_tnode(func_var)
                func_def_tnode = self.find_function_def(func_tnode)
                return TypeFailFunction(tuple(func_type.__args__), func_def_tnode, node)
            else:
                func_type = new_func_type
        elif len(func_type.__args__) - 1 != len(arg_types):
            func_tnode = self.get_tnode(func_var)
            func_def_tnode = self.find_function_def(func_tnode)
            return TypeFailFunction((func_type, ), func_def_tnode, node)

        # Substitute polymorphic type variables
        new_tvars = {tvar: self.fresh_tvar(node) for tvar in getattr(func_type, 'polymorphic_tvars', [])}
        new_func_type = literal_substitute(func_type, new_tvars)
        results = []
        for i in range(len(arg_types)):
            result = self.unify(arg_types[i], new_func_type.__args__[i], node)
            if isinstance(result, TypeFail):
                results.append(i)
        if results:
            func_tnode = self.get_tnode(func_var)
            func_def_tnode = self.find_function_def(func_tnode)
            return TypeFailFunction((new_func_type, ), func_def_tnode, node, results)
        return self._type_eval(new_func_type.__args__[-1])

    def _type_eval(self, t) -> TypeResult:
        """Evaluate a type. Used for tuples."""
        if isinstance(t, TuplePlus):
            return t.eval_type(self)
        if isinstance(t, TypeVar):
            return self.resolve(t)
        if isinstance(t, GenericMeta) and t.__args__ is not None:
            inf_args = (self._type_eval(argument) for argument in t.__args__)
            return wrap_container(_gorg(t), *inf_args)
        else:
            return TypeInfo(t)

    # HELPER METHODS
    def types_in_callable(self, callable_function: Callable) -> Tuple[List[type], type]:
        """Return a tuple of types corresponding to the Callable function's arguments and return value, respectively.
        Used only for testing purposes
        """
        arg_type_lst = [self.resolve(argument).getValue() for argument in callable_function.__args__]
        return arg_type_lst[:-1], arg_type_lst[-1]


def literal_substitute(t, type_map):
    """Make substitutions in t according to type_map, returning resulting type."""
    if isinstance(t, TypeVar) and t.__name__ in type_map:
        return type_map[t.__name__]
    elif isinstance(t, TuplePlus):
        subbed_args = [literal_substitute(t1, type_map) for t1 in t.__constraints__]
        return TuplePlus('tup+', *subbed_args)
    elif isinstance(t, CallableMeta):
        args = list(literal_substitute(t1, type_map) for t1 in t.__args__[:-1])
        res = literal_substitute(t.__args__[-1], type_map)
        new_t = Callable[args, res]
        if hasattr(t, 'polymorphic_tvars'):
            new_t.polymorphic_tvars = t.polymorphic_tvars
        return new_t
    elif isinstance(t, GenericMeta) and t.__args__ is not None:
        return _gorg(t)[tuple(literal_substitute(t1, type_map) for t1 in t.__args__)]
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
    def __init__(self,
                 locals_: Optional[Dict[str, type]] = None,
                 nonlocals_: Optional[Dict[str, type]] = None,
                 globals_: Optional[Dict[str, type]] = None):
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

    def create_in_env(self, type_constraints, environment, variable_name, node) -> None:
        """Helper to create a fresh Type Var and adding the variable to appropriate environment."""
        if environment == 'locals':
            self.locals[variable_name] = type_constraints.fresh_tvar(node)
        elif environment == 'globals':
            self.globals[variable_name] = type_constraints.fresh_tvar(node)
        elif environment == 'nonlocals':
            self.nonlocals[variable_name] = type_constraints.fresh_tvar(node)

    def __str__(self):
        return str(self.locals)


###############################################################################
# Parsing type annotations
###############################################################################
def parse_annotations(node: NodeNG, class_tvars=None):
    """Return a type specified by the type annotations for a node."""
    if isinstance(node, astroid.FunctionDef):
        arg_types = []
        no_class_tvars = class_tvars is None
        is_methodcall = isinstance(node.parent, astroid.ClassDef)
        if no_class_tvars and is_methodcall:
            self_type = _node_to_type(node.parent.name)
        elif no_class_tvars or not is_methodcall:
            self_type = None
        elif node.parent.name in _BUILTIN_TO_TYPING:
            self_type = eval(_BUILTIN_TO_TYPING[node.parent.name])[tuple(_node_to_type(tv) for tv in class_tvars)]
        else:
            self_type = _node_to_type(node.parent.name)

        for arg, annotation in zip(node.args.args, node.args.annotations):
            if getattr(arg, 'name', None) == 'self' and annotation is None:
                arg_types.append(self_type)
            else:
                arg_types.append(_node_to_type(annotation))

        rtype = _node_to_type(node.returns)
        return create_Callable(arg_types, rtype, class_tvars), node.type
    elif isinstance(node, astroid.AssignName) and isinstance(node.parent, astroid.AnnAssign):
        return _node_to_type(node.parent.annotation), 'attribute'


def _node_to_type(node: NodeNG, locals=None) -> type:
    """Return a type represented by the input node."""
    locals = locals or _TYPESHED_TVARS
    if node is None:
        return Any
    elif isinstance(node, str):
        try:
            return eval(node, globals(), locals)
        except:
            return _ForwardRef(node)
    elif isinstance(node, astroid.Name):
        try:
            return eval(node.name, globals(), locals)
        except:
            return _ForwardRef(node.name)
    elif isinstance(node, astroid.Subscript):
        v = _node_to_type(node.value)
        s = _node_to_type(node.slice)
        return v[s]
    elif isinstance(node, astroid.Index):
        return _node_to_type(node.value)
    elif isinstance(node, astroid.Tuple):
        return tuple(_node_to_type(t) for t in node.elts if not isinstance(t, astroid.Ellipsis))
    elif isinstance(node, astroid.List):
        return [_node_to_type(t) for t in node.elts if not isinstance(t, astroid.Ellipsis)]
    elif isinstance(node, astroid.Const) and node.value is None:
        return None
    else:
        return node


def class_callable(init):
    """Convert an __init__ type signature into a callable for the class."""
    return create_Callable(
        init.__args__[1:-1], init.__args__[0], init.polymorphic_tvars
    )
