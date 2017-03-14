import ast
from _ast import *
import astroid.inference
import astroid
from astroid.node_classes import *
from typing import *
from typing import TupleMeta, GenericMeta, UnionMeta, _gorg, _geqv
from astroid.transforms import TransformVisitor
from ..typecheck.base import op_to_dunder, TuplePlus, lookup_method, fresh_tvar


class TypeInferenceError(Exception):
    pass


class NoType:
    pass


class TypeInfo:
    """A class representing the inferred type of a value.

    === Instance attributes ===
    - type (type): type of the inferred value
    - context (Dict[str, type]): dictionary of variable names to their types
    """
    def __init__(self, type_, context=None):
        self.type = type_
        if context is None:
            self.context = {}
        else:
            self.context = context


def unify(type1, type2):
    """Unify two different types."""
    if isinstance(type1, TypeVar) and isinstance(type2, TypeVar):
        return {type1.__name__: type2.__name__}
    elif isinstance(type1, TypeVar):
        constraints = type1.__constraints__
        if not constraints:
            return {type1.__name__: type2}

        for constraint in constraints:
            try:
                tmap = unify(type2, constraint)
            except TypeInferenceError:
                continue
            unify_map(tmap, {type1.__name__: type2})
            return tmap
        else:
            raise TypeInferenceError('bad unify')
    elif isinstance(type2, TypeVar):
        return unify(type2, type1)
    elif isinstance(type1, GenericMeta) and isinstance(type2, GenericMeta):
        if not _geqv(type1, type2):
            raise TypeInferenceError('bad unify')

        if type1.__args__ is None or type2.__args__ is None:
            return {}

        tmap = {}
        for a1, a2 in zip(type1.__args__, type2.__args__):
            new_tmap = unify(substitute(a1, tmap), substitute(a2, tmap))
            unify_map(tmap, new_tmap)
        return tmap
    # Handle tuples differently
    elif isinstance(type1, TupleMeta) and isinstance(type2, TupleMeta):
        tup1, tup2 = type1.__tuple_params__, type2.__tuple_params__
        i = 0
        tmap = {}
        while i < len(tup1) - 1 and i < len(tup2) - 1:
            new_tmap = unify(tup1[i], tup2[i])
            unify_map(tmap, new_tmap)
        if len(tup1) == len(tup2):
            new_tmap = unify(tup1[i], tup2[i])
            unify_map(tmap, new_tmap)
        elif len(tup1) < len(tup2) and isinstance(tup1[i], TypeVar):
            unify_map(tmap, {tup1[i].__name__: tup2[i:]})
        elif len(tup2) < len(tup1) and isinstance(tup2[i], TypeVar):
            unify_map(tmap, {tup2[i].__name__: tup1[i:]})
        else:
            raise TypeInferenceError('unable to unify Tuple types')
        return tmap
    elif type1 == type2:
        return {}
    else:
        raise TypeInferenceError('bad unify')


def substitute(t, type_map):
    """Make substitutions in t according to type_map, returning resulting type."""
    if isinstance(t, TypeVar) and t.__name__ in type_map:
        return type_map[t.__name__]
    elif isinstance(t, GenericMeta) and t.__args__ is not None:
        return _gorg(t)[tuple(substitute(t1, type_map) for t1 in t.__args__)]
    elif isinstance(t, TuplePlus):
        tup = ()
        for c in t.__constraints__:
            tup = tup + type_map[c.__name__]  # assume c is mapped to a (Python) tuple
        return Tuple[tup]
    else:
        return t


def unify_call(func_type, *arg_types):
    """Unify a function call with the given function type and argument types.

    Return a unification map and result type.
    """
    param_types, return_type = func_type.__args__, func_type.__result__
    # Check that the number of parameters matches the number of arguments.
    if len(param_types) != len(arg_types):
        raise TypeInferenceError('Wrong number of arguments')

    tmap = {}
    for arg_type, param_type in zip(arg_types, param_types):
        new_tmap = unify(arg_type, param_type)
        unify_map(tmap, new_tmap)

    return tmap, substitute(return_type, tmap)


def unify_map(tmap, new_tmap):
    for k, v in new_tmap.items():
        if k not in tmap:
            tmap[k] = v
        else:
            v1 = tmap[k]
            if issubclass(v1, v):
                tmap[k] = v
            elif not issubclass(v, v1):
                tmap[k] = Any


class TypeErrorInfo:
    """Class representing an error in type inference."""
    def __init__(self, msg, node):
        self.msg = msg
        self.node = node


##############################################################################
# Literals
##############################################################################
def set_const_type_constraints(node):
    """Populate type constraints for astroid nodes for num/str/bool/None/bytes literals."""
    node.type_constraints = TypeInfo(type(node.value))


def set_tuple_type_constraints(node):
    # node_types contains types of elements inside tuple.
    node.type_constraints = TypeInfo(
        Tuple[tuple(x.type_constraints.type for x in node.elts)]
    )


def set_list_type_constraints(node):
    # node_types contains types of elements inside list.
    node_types = {node_child.type_constraints.type for node_child in node.elts}
    # If list has more than one type, just set node.type_constraints to List.
    # If list has only one type T, set the node.type_constraints to be List[T].
    if len(node_types) == 1:
        # node_types.pop() returns the only element in the set, which is a
        # type object.
        node.type_constraints = TypeInfo(List[node_types.pop()])
    else:
        node.type_constraints = TypeInfo(List[Any])


def set_dict_type_constraints(node):
    # node_types contains types of elements inside Dict.
    key_types = {key.type_constraints.type for key, _ in node.items}
    value_types = {value.type_constraints.type for _, value in node.items}

    # If all the keys have the same type and all the values have the same type,
    # set the type constraint to a Dict of the two types.
    # Else, just use the general Dict type.
    if len(key_types) == 1 and len(value_types) == 1:
        node.type_constraints = TypeInfo(Dict[key_types.pop(), value_types.pop()])
    else:
        node.type_constraints = TypeInfo(Dict)


def set_index_type_constraints(node):
    node.type_constraints = node.value.type_constraints


def set_expr_type_constraints(node):
    """Expr nodes take the value of their child
    """
    node.type_constraints = node.value.type_constraints


def set_name_type_constraints(node):
    t = fresh_tvar()
    node.type_constraints = TypeInfo(t, {node.name: t})


##############################################################################
# Operation nodes
##############################################################################
def set_binop_type_constraints(node):
    left_type = node.left.type_constraints.type
    right_type = node.right.type_constraints.type
    op_name = op_to_dunder(node.op)

    try:
        method_type = lookup_method(left_type, op_name)
    except KeyError:
        node.type_constraints = TypeInfo(
            TypeErrorInfo('Method {}.{} not found'.format(left_type, op_name), node)
        )
        return

    try:
        _, return_type = unify_call(method_type, left_type, right_type)
    except TypeInferenceError as e:
        node.type_constraints = TypeInfo(
            TypeErrorInfo('incompatible types {} and {} in BinOp'.format(left_type, right_type), node)
        )
    else:
        node.type_constraints = TypeInfo(return_type)


def set_unaryop_type_constraints(node):
    node.type_constraints = node.operand.type_constraints


def set_subscript_type_constraints(node):
    if hasattr(node.value, 'type_constraints') and hasattr(node.slice, 'type_constraints'):
        value_type = node.value.type_constraints.type
        arg_type = node.slice.type_constraints.type
        op_name = '__getitem__'

        try:
            method_type = lookup_method(left_type, op_name)
        except KeyError:
            node.type_constraints = TypeInfo(
                TypeErrorInfo('Method {}.{} not found'.format(left_type, op_name), node)
            )
            return

        try:
            _, return_type = unify_call(method_type, value_type, arg_type)
        except TypeInferenceError as e:
            node.type_constraints = TypeInfo(
                TypeErrorInfo('incompatible types {} and {} in Subscript'.format(value_type, arg_type), node)
            )
        else:
            node.type_constraints = TypeInfo(return_type)


# TODO: Add check in the set_compare_type_constraints as in BinOp.
def set_compare_type_constraints(node):
    """Compare operators includes:
    '<', '>', '==', '>=', '<=', '<>', '!=', 'is' ['not'], ['not'] 'in' """
    node.type_constraints = TypeInfo(bool)


def set_boolop_type_constraints(node):
    """Boolean operators includes: 'and', 'or'
    Logic of Boolean Operations:
    x or y --> if x is false, then y, else x
    x and y --> if x is false, then x, else y
    """
    if node.op == 'or':
        if not node.values[0]:
            node.type_constraints = node.values[1].type_constraints
        else:
            node.type_constraints = node.values[0].type_constraints
    elif node.op == 'and':
        if not node.values[0]:
            node.type_constraints = node.values[0].type_constraints
        else:
            node.type_constraints = node.values[1].type_constraints



# Assignment
def set_assign_type_constraints(node):
    first_target = node.targets[0]
    node.type_constraints = TypeInfo(NoType, {first_target.name: (node.value.type_constraints)})


def set_module_type_constraints(node):
    names = {k: NoType for k in node.globals.keys()}
    for s in node.body:
        if s.is_statement and isinstance(s.type_constraints, tuple) and len(s.type_constraints) > 1:
            for identifier, type_constraint in s.type_constraints[1].items():
                if identifier in names:
                    names[identifier] = type_constraint
    node.type_constraints = TypeInfo(NoType, names)


def register_type_constraints_setter():
    """Instantiate a visitor to transform the nodes.
    Register the transform functions on an instance of TransformVisitor.
    """
    type_visitor = TransformVisitor()
    type_visitor.register_transform(astroid.Const, set_const_type_constraints)
    type_visitor.register_transform(astroid.Tuple, set_tuple_type_constraints)
    type_visitor.register_transform(astroid.List, set_list_type_constraints)
    type_visitor.register_transform(astroid.Dict, set_dict_type_constraints)
    type_visitor.register_transform(astroid.Name, set_name_type_constraints)
    type_visitor.register_transform(astroid.BinOp, set_binop_type_constraints)
    type_visitor.register_transform(astroid.UnaryOp,
                                    set_unaryop_type_constraints)
    type_visitor.register_transform(astroid.Index,
                                    set_index_type_constraints)
    type_visitor.register_transform(astroid.Subscript,
                                    set_subscript_type_constraints)
    type_visitor.register_transform(astroid.Compare,
                                    set_compare_type_constraints)
    type_visitor.register_transform(astroid.BoolOp,
                                    set_boolop_type_constraints)
    type_visitor.register_transform(astroid.Expr,
                                    set_expr_type_constraints)
    type_visitor.register_transform(astroid.Assign,
                                    set_assign_type_constraints)
    type_visitor.register_transform(astroid.Module,
                                    set_module_type_constraints)
    return type_visitor
