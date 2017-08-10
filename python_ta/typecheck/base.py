from typing import *
from typing import CallableMeta, GenericMeta, TupleMeta, _gorg, _geqv, _type_vars, _ForwardRef, IO
import astroid


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
        t1 = type_constraints.lookup_concrete(t1)
        t2 = type_constraints.lookup_concrete(t2)
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


class TNode:
    def __init__(self, node_type, origin_node=None):
        self.type = node_type
        self.origin = origin_node
        self.parent = None


class TypeConstraints:
    """Represents all the type constraints in the program."""
    def __init__(self):
        self._count = 0
        self._sets = []
        self._tvar_tnode = {}

    def clear_tvars(self):
        """Resets the type constraints kept track of in the program."""
        self._count = 0
        self._sets = []
        self._tvar_tnode = {}

    def make_set(self, value, origin_node=None):
        tn = TNode(value, origin_node)
        return tn

    def _find_rep(self, node: TNode):
        while node.parent is not None or (node.parent and node != node.parent):
            node = node.parent
        return node

    def _union(self, node1: TNode, node2: TNode):
        rep1 = self._find_rep(node1)
        rep2 = self._find_rep(node2)
        if isinstance(rep1.type, TypeVar) and isinstance(rep2.type, TypeVar):
            rep2.parent = rep1
        elif isinstance(rep2.type, TypeVar):
            rep2.parent = rep1
        elif isinstance(rep1.type, TypeVar):
            rep1.parent = rep2

    def fresh_tvar(self, node) -> TypeVar:
        """Return a fresh type variable with the node it was created in."""
        tvar = TypeVar('_T' + str(self._count))
        tnode = self.make_set(tvar, origin_node=node)
        self._sets.append(tnode)
        self._tvar_tnode[tvar] = tnode
        self._count += 1
        return tvar

    def add_concrete_to_sets(self, _type):
        """Add a concrete type to the type constraints sets."""
        tnode = self.make_set(_type)
        self._sets.append(tnode)
        return tnode

    def unify(self, t1, t2):
        if isinstance(t1, TypeVar) and isinstance(t2, TypeVar):
            if t1 == t2:
                # TODO: look into implementation of  __eq__ TVARS
                pass
            else:
                node1, node2 = self._tvar_tnode[t1], self._tvar_tnode[t2]
                self._union(node1, node2)
        elif isinstance(t1, TypeVar):
            node2 = self.add_concrete_to_sets(t2)
            node1 = self._tvar_tnode[t1]
            self._union(node1, node2)
        elif isinstance(t2, TypeVar):
            self.unify(t2, t1)
        elif isinstance(t1, GenericMeta) and isinstance(t2, GenericMeta):
            self._unify_generic(t1, t2)
        elif isinstance(t1, CallableMeta) and isinstance(t2, CallableMeta):
            rtype = self.unify_call(t1, *t2.__args__[:-1])
            self.unify(rtype, t2.__args__[-1])
        elif isinstance(t1, TupleMeta) and isinstance(t2, TupleMeta):
            self._unify_tuple(t1, t2)
        elif t1.__class__.__name__ == '_Union' or t2.__class__.__name__ == '_Union':
            pass
        elif t1 == Any or t2 == Any:
            pass
        elif isinstance(t1, _ForwardRef) and isinstance(t2, _ForwardRef) and t1 == t2:
            pass
        elif isinstance(t1, _ForwardRef) or isinstance(t2, _ForwardRef):
            raise Exception(str(t1) + ' ' + str(t2))
        elif issubclass(t1, t2) or issubclass(t2, t1):
            pass
        elif t1 != t2:
            raise TypeInferenceError(str(t1) + ' ' + str(t2))

    def _unify_generic(self, t1: GenericMeta, t2: GenericMeta):
        """Unify two generic-typed nodes."""
        if not _geqv(t1, t2):
            raise TypeInferenceError('bad unify')
        elif t1.__args__ is not None and t2.__args__ is not None:
            for a1, a2 in zip(t1.__args__, t2.__args__):
                self.unify(a1, a2)

    def _unify_tuple(self, t1, t2):
        tup1, tup2 = t1.__tuple_params__, t2.__tuple_params__
        if not tup1 or not tup2:
            return
        elif len(tup1) != len(tup2):
            raise TypeInferenceError('unable to unify Tuple types')
        else:
            for elem1, elem2 in zip(tup1, tup2):
                self.unify(elem1, elem2)

    def unify_call(self, func_type, *arg_types, node=None):
        """Unify a function call with the given function type and argument types.

        Return a result type.
        """
        # Check that the number of parameters matches the number of arguments.
        if len(func_type.__args__) - 1 != len(arg_types):
            raise TypeInferenceError('Wrong number of arguments')

        # Substitute polymorphic type variables
        new_tvars = {tvar: self.fresh_tvar(node) for tvar in getattr(func_type, 'polymorphic_tvars', [])}
        new_func_type = literal_substitute(func_type, new_tvars)
        for arg_type, param_type in zip(arg_types, new_func_type.__args__[:-1]):
            self.unify(arg_type, param_type)
        return self._type_eval(new_func_type.__args__[-1])

    def least_general_unifier(self, t1, t2):
        if isinstance(t1, TypeVar) and isinstance(t2, TypeVar):
            i1 = self._find(t1)
            i2 = self._find(t2)
            if issubclass(i1, i2):
                return i2
            elif issubclass(i2, i1):
                return i1
            else:
                return Any
        elif isinstance(t1, TypeVar):
            i1 = self._find(t1)
            if issubclass(i1, t2):
                return t2
            elif issubclass(t2, i1):
                return i1
            else:
                return Any
        elif isinstance(t2, TypeVar):
            return self.least_general_unifier(t2, t1)
        elif isinstance(t1, GenericMeta) and isinstance(t2, GenericMeta):
            return self._least_general_unifier_generic(t1, t2)
        elif isinstance(t1, CallableMeta) and isinstance(t2, CallableMeta):
            rtype = self._least_general_unifier_call(t1, *t2.__args__[:-1])
            return self.least_general_unifier(rtype, t2.__args__[-1])
        elif isinstance(t1, TupleMeta) and isinstance(t2, TupleMeta):
            return self._least_general_unifier_tuple(t1, t2)
        elif t1.__class__.__name__ == '_Union' or t2.__class__.__name__ == '_Union':
            pass
        elif t1 == Any or t2 == Any:
            return Any
        elif issubclass(t1, t2):
            return t2
        elif issubclass(t2, t1):
            return t1
        elif t1 != t2:
            return Any

    def _least_general_unifier_generic(self, t1: GenericMeta, t2: GenericMeta):
        """Unify two generic types."""
        if not _geqv(t1, t2):
            raise TypeInferenceError('bad unify')
        elif t1.__args__ is not None and t2.__args__ is not None:
            for a1, a2 in zip(t1.__args__, t2.__args__):
                return self.least_general_unifier(a1, a2)

    def _least_general_unifier_tuple(self, t1: TupleMeta, t2: TupleMeta):
        tup1, tup2 = t1.__tuple_params__, t2.__tuple_params__
        if not tup1 or not tup2:
            return
        elif len(tup1) != len(tup2):
            raise TypeInferenceError('unable to unify Tuple types')
        else:
            for elem1, elem2 in zip(tup1, tup2):
                return self.least_general_unifier(elem1, elem2)

    def _least_general_unifier_call(self, func_type, *arg_types):
        # TODO: Test this helper.
        if len(func_type.__args__) - 1 != len(arg_types):
            raise TypeInferenceError('Wrong number of arguments')
        new_tvars = {tvar: self.fresh_tvar() for tvar in getattr(func_type, 'polymorphic_tvars', [])}
        new_func_type = literal_substitute(func_type, new_tvars)
        for i in range(len(list(zip(arg_types, new_func_type.__args__[:-1])))):
            new_func_type.__args__[i] = self.least_general_unifier(arg_types[i], new_func_type.__args__[i])
        return self._type_eval(new_func_type.__args__[-1])

    def _type_eval(self, t):
        """Evaluate a type. Used for tuples."""
        if isinstance(t, TuplePlus):
            return t.eval_type(self)
        if isinstance(t, TypeVar):
            return self.lookup_concrete(t)
        if isinstance(t, GenericMeta) and t.__args__ is not None:
            return _gorg(t)[tuple(self._type_eval(argument) for argument in t.__args__)]
        else:
            return t

    def lookup_concrete(self, tvar):
        """Find a set representative, which is either a concrete type, or the first element."""
        if not isinstance(tvar, TypeVar):
            return tvar

        tnode = self._tvar_tnode[tvar]
        return self._find_rep(tnode).type

    ### HELPER METHODS
    def types_in_callable(self, callable_function):
        """Return a tuple of types corresponding to the Callable function's arguments and return value, respectively."""
        arg_type_lst = [self.lookup_concrete(argument) for argument in callable_function.__args__]
        return arg_type_lst[:-1], arg_type_lst[-1]

    def can_unify(self, t1, t2):
        """Return true iff given argument types can be unified."""
        if isinstance(t1, TypeVar) or isinstance(t2, TypeVar):
            return True
        elif isinstance(t1, GenericMeta) and isinstance(t2, GenericMeta):
            if not _geqv(t1, t2):
                return False
            elif t1.__args__ is not None and t2.__args__ is not None:
                for a1, a2 in zip(t1.__args__, t2.__args__):
                    if not self.can_unify(a1, a2):
                        return False
                return True
            else:
                return False
        elif isinstance(t1, GenericMeta):
            return False
        elif isinstance(t2, GenericMeta):
            return False
        elif t1.__class__.__name__ == '_Union' and t2.__class__.__name__ == 'Union':
            for union_type in t1.__args__:
                if union_type in t2.__args__:
                    return True
            else:
                return False
        elif t1.__class__.__name__ == '_Union':
            if t2 in t1.__args__:
                return True
            else:
                return False
        elif t2.__class__.__name__ == '_Union':
            if t1 in t2.__args__:
                return True
            else:
                return False
        elif t1 == Any or t2 == Any:
            return True
        elif (hasattr(t1, 'msg') and ('not found' in t1.msg)) or (hasattr(t2, 'msg') and ('not found' in t2.msg)):
            return False
        elif isinstance(t1, _ForwardRef) and isinstance(t2, _ForwardRef) and t1 == t2:
            return True
        elif isinstance(t1, _ForwardRef) or isinstance(t2, _ForwardRef):
            return False
        elif issubclass(t1, t2) or issubclass(t2, t1):
            return True
        elif t1 != t2:
            return False
        else:
            return True


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
