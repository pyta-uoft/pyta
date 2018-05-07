import sys
from typing import *
from typing import CallableMeta, GenericMeta, TupleMeta, _ForwardRef, IO
import typing
import astroid
from astroid.node_classes import NodeNG


class TypeResult(Failable):
    """
    Represents the result of a type check operation that either succeeded or
    failed.
    """
    def __init__(self, value):
        super.__int__(value)
        

class TypeInfo(TypeResult):
    """
    Represents the result of a successful type check operation
    Contains information about the inferred type of a node
    """

    def __init__(self, type_: type):
        super.__init__(type_)

    def __eq__(self, other): # TODO: inherit this
        if not isinstance(other, TypeResult):
            return False
        return super.__eq__(other)

    def __str__(self):
        return f'TypeInfo: {self.value}'


class TypeFail(TypeResult): 
    """
    Represents the result of a failed type check operation
    Contains error message
    """
    def __init__(self, msg: str):
        if not isinstance(msg, str):
            raise TypeError
        super(TypeResult, self).__init__(msg)

    def __eq__(self, other): # TODO: inherit this
        if not isinstance(other, TypeFail):
            return False
        return super.__eq__(other)
        
    def __str__(self):
        return f'TypeFail: {self.value}'

    def bind(self, _):
        return self


# Make _gorg compatible for Python 3.6.2 and 3.6.3.
def _gorg(x):
    if sys.version_info < (3, 6, 3):
        return typing._gorg(x)
    else:
        return x._gorg


class TypeInferenceError(Exception):
    pass

Num = TypeVar('number', int, float)
a = TypeVar('a')
MulNum = TypeVar('mul_n', int, float, str, List[a])
tup1 = TypeVar('tup1')
tup2 = TypeVar('tup2')


class TuplePlus(TypeVar, _root=True):
    def eval_type(self, type_constraints: 'TypeConstraints'):
        t1, t2 = self.__constraints__
        t1 = type_constraints.resolve(t1)
        t2 = type_constraints.resolve(t2)
        return Tuple[t1.__tuple_params__ + t2.__tuple_params__]


class TupleSubscript(TypeVar, _root=True):
    pass


def create_Callable(args: Iterable[type], rtype, poly_vars=None):
    poly_vars = poly_vars or []
    c = Callable[list(args), rtype]
    c.polymorphic_tvars = poly_vars
    return c


TYPE_SIGNATURES = {
    int: {
        '__add__': create_Callable([int, Num], Num, [Num]),
        '__sub__': create_Callable([int, Num], Num, [Num]),
        '__mul__': create_Callable([int, MulNum], MulNum, [MulNum]),
        '__idiv__': create_Callable([int, Num], Num, [Num]),
        '__mod__': create_Callable([int, Num], Num, [Num]),
        '__pow__': create_Callable([int, Num], Num, [Num]),
        '__div__': create_Callable([int, Num], float, [Num]),
    },
    float: {
        '__add__': create_Callable([float, Num], float, [Num]),
        '__sub__': create_Callable([float, Num], float, [Num]),
        '__mul__': create_Callable([float, Num], float, [Num]),
        '__idiv__': create_Callable([float, Num], float, [Num]),
        '__mod__': create_Callable([float, Num], float, [Num]),
        '__pow__': create_Callable([float, Num], float, [Num]),
        '__div__': create_Callable([float, Num], float, [Num]),
    },
    str: {
        '__add__': Callable[[str, str], str],
        '__mul__': Callable[[str, int], str]
    },
    List: {
        '__add__': create_Callable([List[a], List[a]], List[a], [a]),
        '__mul__': create_Callable([List[a], int], List[a], [a]),
        '__getitem__': create_Callable([List[a], int], a, [a])
    },
    Tuple: {
        '__add__': create_Callable([tup1, tup2], TuplePlus('tup+', tup1, tup2), [tup1, tup2]),
    }
}


def op_to_dunder_binary(op):
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


def op_to_dunder_unary(op):
    """Return the dunder method name corresponding to unary op."""
    if op == '-':
        return '__neg__'
    elif op == '+':
        return '__pos__'
    elif op == '~':
        return '__invert__'
    else:
        return op


def lookup_method(name, caller_type, *args):
    """Lookup method with the given name for the given type."""
    if isinstance(caller_type, TupleMeta):
        caller_origin = Tuple
    elif isinstance(caller_type, GenericMeta):
        caller_origin = _gorg(caller_type)
    else:
        caller_origin = caller_type

    return TYPE_SIGNATURES[caller_origin][name]


class _TNode:
    """A node in the TypeConstraints disjoint set data structure."""
    type: type
    origin: Optional[NodeNG]
    parent: Optional['_TNode']

    def __init__(self, node_type: type, origin_node: Optional[NodeNG] = None):
        self.type = node_type
        self.origin = origin_node
        self.parent = None


class TypeConstraints:
    """Represents all the type constraints in the program.

    This is mainly comprised of a disjoint set data structure, in which each disjoint set
    represents a set of equivalences of type variables and concrete types. The nodes
    in the disjoint set are implemented by the private class _TNode above.
    """
    # The number of type variables stored in the data structure. Used to generate fresh type variables.
    _count: int
    # The disjoint sets.
    _nodes: List[Set[_TNode]]
    # A mapping of type variable names to nodes.
    _tvar_to_tnode: Dict[str, _TNode]

    def __init__(self):
        self.reset()

    def reset(self):
        """Reset the type constraints kept track of in the program."""
        self._count = 0
        self._nodes = []
        self._tvar_to_tnode = {}


    ###########################################################################
    # Creating new nodes ("make set")
    ###########################################################################
    # TODO: Rename to better distinguish between _TNodes and AST Nodes
    def fresh_tvar(self, node: Optional[NodeNG] = None) -> TypeVar:
        """Create and return a fresh type variable, associated with the given node.
        """
        tvar = TypeVar(f'_T{self._count}')
        self._count += 1
        self._make_set(tvar, origin_node=node)
        return tvar

    def _make_set(self, t: type, origin_node: Optional[NodeNG] = None) -> _TNode:
        node = _TNode(t, origin_node)
        self._nodes.append(node)
        if isinstance(t, TypeVar):
            self._tvar_to_tnode[t] = node
        return node

    ###########################################################################
    # Type lookup ("find")
    ###########################################################################
    def resolve(self, t: type) -> type:
        """
        TODO: resolve :: type -> TypeResult

        Return the type associated with the given type.

        If t is a type variable that is associated with a concrete (non-TypeVar) type, return the concrete type.
        Otherwise if the type variable with the smallest name is returned (using < to compare strings).
        """
        # TODO: Make this recursive, e.g. if `t` is List[TypeVar('a')], the contained TypeVar should be resolved.
        if isinstance(t, TypeVar):
            return self._find(t).type
        else:
            return t

    def _find(self, tv: TypeVar) -> _TNode:
        """Return the disjoint set node associated with the given type variable."""
        node = self._tvar_to_tnode[tv]
        while node.parent is not None or (node.parent and node != node.parent):
            node = node.parent
        return node

    ###########################################################################
    # Type unification ("union")
    ###########################################################################
    def unify(self, t1: TypeResult, t2: TypeResult) -> TypeResult:
        """
        TODO: type -> type -> TypeResult

        Unify the given types.
        Return the result of the unification, or an error
        message if the types can't be unified.
        """
        # Case of TypeFail instance
        # Propogate error upward
        if isinstance(t1, TypeFail):
            return t1 >> (lambda x: TypeFail(x))
        elif isinstance(t2, TypeFail):
            return t2 >> (lambda x: TypeFail(x))

        # Case of TypeVars
        elif isinstance(t1.getValue(), TypeVar) and isinstance(t2.getValue(), TypeVar):
            result = self._merge_sets(t1.getValue(), t2.getValue())
            if not isinstance(result, str):
                return TypeInfo(self.resolve(t1.getValue()))
            else:
                return TypeFail(result)
        # Case of two generics
        # TODO: Change this to use binds instead of always looking up values
        # Currenly only accounts for lists
        elif isinstance(t1.getValue(), GenericMeta) and isinstance(
                t2.getValue(), GenericMeta):
            # Bind GenericMeta object from each TypeInfo to x and y,
            # pass to unify_generic
            return t1 >> (lambda x: t2 >> (lambda y: self._unify_generic(x, y)))

        # Case of generic and non-generic
        elif isinstance(t1.getValue(), GenericMeta) or isinstance(
                t2.getValue(), GenericMeta):
            return TypeFail("Cannot unify generic with primitive")

        elif isinstance(t1.getValue(), TypeVar):
            rep1 = self._find(t1.getValue())
            if rep1.type == t1.getValue():
                # Simply make t2 the set representative for t1.
                rep1.parent = self._make_set(t2.getValue())
                return t2
            else:
                return self.unify(TypeInfo(rep1.type), t2)
        elif isinstance(t2.getValue(), TypeVar):
            return self.unify(t2, t1)

        # elif t1.__class__.__name__ == '_Union' or t2.__class__.__name__ == '_Union':
        #     return t1
        # elif t1 == Any or t2 == Any:
        #     return t1
        elif isinstance(t1.getValue(), _ForwardRef) and isinstance(
                t2.getValue(), _ForwardRef) and t1 == t2:
            return t1
        elif isinstance(t1.getValue(), _ForwardRef) or isinstance(
                t1.getValue(), _ForwardRef):
            return TypeFail("Attempted to unify forwardref  with non-ref")

        # Case of unifying two concrete types
        elif t1.getValue() == t2.getValue():
            return t1
        elif t1 != t2:
            return TypeFail(
                f'Incompatible Types {t1.getValue()} and {t2.getValue()}')

    def _unify_generic(self, t1: GenericMeta, t2: GenericMeta) -> TypeResult:
        g1, g2 = _gorg(t1), _gorg(t2)
        if g1 != g2:
            return TypeFail(f'Incompatible generic types {_gorg(t1)} and {_gorg(t2)}')
        if len(t1.__args__) != len(t2.__args__):
            return TypeFail(f'Generic types {_gorg(t1)} and {_gorg(t2)} must have the same number of args')
         
        unify_result = failable_collect([self.unify(a1, a2) for a1, a2 in zip(t1.__args__, t2.__args__)])
        if type(unify_result) == TypeFail:
            return unify_result
        unified_args = unify_result.getValue()
        
        if g1 == Tuple:
            tuple_args = tuple(unified_args)
            # Handle the special case when t1 or t2 are empty tuples; TODO: investigate this
            if tuple_args == ((),):
                tuple_args = ()
            return TypeInfo(Tuple[tuple_args])
        elif g1 == Callable:
            return TypeInfo(g1[unified_args[:-1], unified_args[-1]])
        else:
            return g1[tuple(unified_args)]
            

    def _merge_sets(self, t1: TypeVar, t2: TypeVar) -> None:
        """Merge the two sets that t1 and t2 belong to.

        TODO: _merge_sets :: TypeVar -> TypeVar -> TypeResult

        Raise a TypeInferenceError if merging the sets results in incompatible
        concrete types.
        """
        # TODO: look into implementation of  __eq__ for TypeVar to make sure we can use == here.
        if t1 == t2:
            return

        rep1 = self._find(t1)
        rep2 = self._find(t2)
        if isinstance(rep1.type, TypeVar) and isinstance(rep2.type, TypeVar):
            if rep1.type.__name__ < rep2.type.__name__ :
                rep2.parent = rep1
            else:
                rep1.parent = rep2
        elif isinstance(rep2.type, TypeVar):
            rep2.parent = rep1
        elif isinstance(rep1.type, TypeVar):
            rep1.parent = rep2
        else:
            # In this case both set representatives are concrete types.
            # If they're compatible, we can still unify the sets. Otherwise, an error
            # is raised here.
            if rep1.type == rep2.type:
                rep2.parent = rep1
            else:
                return f'Incompatible types {rep1.type} and {rep2.type}'

    ###########################################################################
    # Handling generic polymorphism
    ###########################################################################
    def can_unify(self, t1: type, t2: type) -> bool:
        """Return whether t1 and t2 can unify.

        Don't actually update disjoint set structure though.
        TODO: this doesn't cover all cases. Could replicate unify, but that seems inefficient.
        """
        if isinstance(t1, TypeVar) or isinstance(t2, TypeVar):
            return True
        elif isinstance(t1, GenericMeta) and isinstance(t2, GenericMeta):
            return _gorg(t1) == _gorg(t2) and all(self.can_unify(s1, s2) for s1, s2 in zip(t1.__args__, t2.__args__))
        else:
            return t1 == t2

    def unify_call(self, func_type, *arg_types, node=None):
        """
        TODO: Find out what this does

        Unify a function call with the given function type and argument types.

        Return a result type.
        """
        # Check that the number of parameters matches the number of arguments.
        if len(func_type.__args__) - 1 != len(arg_types):
            raise TypeInferenceError('Wrong number of arguments')

        # Substitute polymorphic type variables
        new_tvars = {tvar: self.fresh_tvar(node) for tvar in getattr(func_type, 'polymorphic_tvars', [])}
        new_func_type = literal_substitute(func_type, new_tvars)
        for arg_type, param_type in zip(arg_types, new_func_type.__args__[:-1]):
            if isinstance(self.unify(arg_type, param_type), str):
                raise TypeInferenceError(f'Incompatible argument types {arg_type} and {param_type}')
        return self._type_eval(new_func_type.__args__[-1])

    def _type_eval(self, t):
        """Evaluate a type. Used for tuples."""
        if isinstance(t, TuplePlus):
            return t.eval_type(self)
        if isinstance(t, TypeVar):
            return self.resolve(t)
        if isinstance(t, GenericMeta) and t.__args__ is not None:
            return _gorg(t)[tuple(self._type_eval(argument) for argument in t.__args__)]
        else:
            return t

    ### HELPER METHODS
    def types_in_callable(self, callable_function):
        """Return a tuple of types corresponding to the Callable function's arguments and return value, respectively."""
        arg_type_lst = [self.resolve(argument) for argument in callable_function.__args__]
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

    TODO:
    """
    def __init__(self,
                 locals_: Optional[Dict[str, type]] = None,
                 nonlocals_: Optional[Dict[str, type]] = None,
                 globals_: Optional[Dict[str, type]] = None):
        """Initialize an environment."""
        self.locals = locals_ or {}
        self.nonlocals = nonlocals_ or {}
        self.globals = globals_ or {}

    def lookup_in_env(self, variable_name):
        """Helper to search for a variable in the environment of a node by name."""
        if variable_name in self.locals:
            return self.locals[variable_name]
        elif variable_name in self.globals:
            return self.globals[variable_name]
        elif variable_name in self.nonlocals:
            return self.nonlocals[variable_name]
        else:
            raise KeyError

    def create_in_env(self, type_constraints, environment, variable_name, node):
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
def parse_annotations(node, class_tvars=None):
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
        return create_Callable(arg_types, rtype, class_tvars)
    elif isinstance(node, astroid.AssignName) and isinstance(node.parent, astroid.AnnAssign):
        return _node_to_type(node.parent.annotation)


def _node_to_type(node, locals=None):
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


def class_callable(init):
    """Convert an __init__ type signature into a callable for the class."""
    return create_Callable(
        init.__args__[1:-1], init.__args__[0], init.polymorphic_tvars
    )
