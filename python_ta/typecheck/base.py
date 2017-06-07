from typing import *
from typing import CallableMeta, GenericMeta, TupleMeta, _gorg, _geqv, _type_vars

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


def create_Callable(args, rtype, poly_vars=None):
    poly_vars = poly_vars or []
    c = Callable[args, rtype]
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


def op_to_dunder(op):
    """Return the dunder method name corresponding to op."""
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
    elif op == 'and':
        return '__and__'
    elif op == 'or':
        return '__or__'
    #TODO: cannot find builtin for not logical operator.
    else:
        return ''


def lookup_method(name, caller_type, *args):
    """Lookup method with the given name for the given type."""
    if isinstance(caller_type, TupleMeta):
        caller_origin = Tuple
    elif isinstance(caller_type, GenericMeta):
        caller_origin = _gorg(caller_type)
    else:
        caller_origin = caller_type

    return TYPE_SIGNATURES[caller_origin][name]


class TypeConstraints:
    """Represents all the type constraints in the program."""
    def __init__(self):
        self._count = 0
        self._sets = []

    def clear_tvars(self):
        """Resets the type constraints kept track of in the program."""
        self._count = 0
        self._sets = []


    def fresh_tvar(self) -> TypeVar:
        """Return a fresh type variable."""
        tvar = TypeVar('_T' + str(self._count))
        self._sets.append({tvar})
        self._count += 1
        return tvar

    def _find(self, t: TypeVar) -> int:
        """Return the index of the set containing t."""
        for i, type_set in enumerate(self._sets):
            if t in type_set:
                return i
        return -1

    def unify(self, t1, t2):
        if isinstance(t1, TypeVar) and isinstance(t2, TypeVar):
            i1 = self._find(t1)
            i2 = self._find(t2)
            if i1 != i2:
                self._sets[i1].update(self._sets[i2])
                self._sets.pop(i2)
        elif isinstance(t1, TypeVar):
            i1 = self._find(t1)
            self._sets[i1].add(t2)
        elif isinstance(t2, TypeVar):
            self.unify(t2, t1)
        elif isinstance(t1, GenericMeta) and isinstance(t2, GenericMeta):
            self._unify_generic(t1, t2)
        elif isinstance(t1, CallableMeta) and isinstance(t2, CallableMeta):
            rtype = self.unify_call(t1, *t2.__args__[:-1])
            self.unify(rtype, t2.__args__[-1])
        elif isinstance(t1, TupleMeta) and isinstance(t2, TupleMeta):
            self._unify_tuple(t1, t2)
        elif t1 != t2:
            raise Exception(str(t1) + ' ' + str(t2))

    def _unify_generic(self, t1: GenericMeta, t2: GenericMeta):
        """Unify two generic types."""
        if not _geqv(t1, t2):
            raise TypeInferenceError('bad unify')
        elif t1.__args__ is not None and t2.__args__ is not None:
            for a1, a2 in zip(t1.__args__, t2.__args__):
                self.unify(a1, a2)

    def _unify_tuple(self, t1: TupleMeta, t2: TupleMeta):
        tup1, tup2 = t1.__tuple_params__, t2.__tuple_params__
        if not tup1 or not tup2:
            return
        elif len(tup1) != len(tup2):
            raise TypeInferenceError('unable to unify Tuple types')
        else:
            for elem1, elem2 in zip(tup1, tup2):
                self.unify(elem1, elem2)

    def unify_call(self, func_type, *arg_types):
        """Unify a function call with the given function type and argument types.

        Return a result type.
        """
        # Check that the number of parameters matches the number of arguments.
        if len(func_type.__args__) - 1 != len(arg_types):
            raise TypeInferenceError('Wrong number of arguments')

        # Substitute polymorphic type variables
        new_tvars = {tvar: self.fresh_tvar() for tvar in getattr(func_type, 'polymorphic_tvars', [])}
        new_func_type = literal_substitute(func_type, new_tvars)
        for arg_type, param_type in zip(arg_types, new_func_type.__args__[:-1]):
            self.unify(arg_type, param_type)
        return self._type_eval(new_func_type.__args__[-1])

    def _type_eval(self, t):
        """Evaluate a type. Used for tuples."""
        if isinstance(t, TuplePlus):
            return t.eval_type(self)
        if isinstance(t, TypeVar):
            return self.lookup_concrete(t)
        if isinstance(t, GenericMeta) and hasattr(t, '__args__'):
            return List[self._type_eval(t.__args__[-1])]
            # TODO: Need to account for other generics? ie. Dictionaries, Tuples
        else:
            return t

    def lookup_concrete(self, tvar):
        """Find a set representative, which is either a concrete type, or the first element."""
        if not isinstance(tvar, TypeVar):
            return tvar

        i = self._find(tvar)
        the_set = self._sets[i]

        rep = None
        for t in the_set:
            if rep is None:
                rep = t
            elif not _type_vars([t]):
                rep = t
            elif (isinstance(t, CallableMeta) or isinstance(t, TuplePlus) or isinstance(t, GenericMeta)) and isinstance(rep, TypeVar):
                rep = t

        if isinstance(rep, CallableMeta):
            return _gorg(rep)[[self.lookup_concrete(t1) for t1 in rep.__args__[:-1]],
                              self.lookup_concrete(rep.__args__[-1])]
        elif isinstance(rep, GenericMeta):
            return _gorg(rep)[tuple(self.lookup_concrete(t1) for t1 in rep.__args__)]
        return rep or tvar

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
                False
        elif t1 != t2:
            return False
        else:
            return True


def literal_substitute(t, type_map):
    """Make substitutions in t according to type_map, returning resulting type."""
    if isinstance(t, TypeVar) and t in type_map:
        return type_map[t]
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

    def create_in_env(self, type_constraints, environment, variable_name):
        """Helper to create a fresh Type Var and adding the variable to appropriate environment."""
        if environment == 'locals':
            self.locals[variable_name] = type_constraints.fresh_tvar()
        elif environment == 'globals':
            self.globals[variable_name] = type_constraints.fresh_tvar()
        elif environment == 'nonlocals':
            self.nonlocals[variable_name] = type_constraints.fresh_tvar()

    def __str__(self):
        return str(self.locals)
