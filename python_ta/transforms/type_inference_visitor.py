import ast
import astroid.inference
import astroid
from astroid.node_classes import *
from typing import *
from typing import CallableMeta, TupleMeta, GenericMeta, UnionMeta, _gorg, _geqv, Optional
from astroid.transforms import TransformVisitor
from ..typecheck.base import op_to_dunder, TuplePlus, lookup_method, Environment, TypeConstraints, TypeInferenceError

TYPE_CONSTRAINTS = TypeConstraints()


class NoType:
    pass


class TypeInfo:
    """A class representing the inferred type of a value.

    === Instance attributes ===
    - type (type): type of the inferred value
    """
    def __init__(self, type_: type):
        self.type = type_


class TypeErrorInfo:
    """Class representing an error in type inference."""
    def __init__(self, msg, node):
        self.msg = msg
        self.node = node

    def __str__(self):
        return self.msg


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
    node.type_constraints = TypeInfo(node.frame().type_environment.locals[node.name])


##############################################################################
# Operation nodes
##############################################################################
def set_binop_type_constraints(node):
    t1 = TYPE_CONSTRAINTS.lookup_concrete(node.left.type_constraints.type)
    t2 = TYPE_CONSTRAINTS.lookup_concrete(node.right.type_constraints.type)
    op_name = op_to_dunder(node.op)

    try:
        method_type = lookup_method(op_name, t1)
    except KeyError:
        node.type_constraints = TypeInfo(
            TypeErrorInfo('Method {}.{} not found'.format(t1, op_name), node)
        )
        return

    try:
        return_type = TYPE_CONSTRAINTS.unify_call(method_type, t1, t2)
    except TypeInferenceError as e:
        node.type_constraints = TypeInfo(
            TypeErrorInfo('incompatible types {} and {} in BinOp'.format(t1, t2), node)
        )
    else:
        node.type_constraints = TypeInfo(return_type)


def set_unaryop_type_constraints(node):
    node.type_constraints = node.operand.type_constraints


def set_subscript_type_constraints(node):
    if hasattr(node.value, 'type_constraints') and hasattr(node.slice, 'type_constraints'):
        value_type = node.value.type_constraints.type
        value_type = TYPE_CONSTRAINTS.lookup_concrete(value_type)
        arg_type = node.slice.type_constraints.type
        op_name = '__getitem__'

        try:
            method_type = lookup_method(op_name, value_type)
        except KeyError:
            node.type_constraints = TypeInfo(
                TypeErrorInfo('Method {}.{} not found'.format(value_type, op_name), node)
            )
            return

        try:
            return_type = TYPE_CONSTRAINTS.unify_call(method_type, value_type, arg_type)
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


##############################################################################
# Statements
##############################################################################
def set_assign_type_constraints(node):
    first_target = node.targets[0]
    TYPE_CONSTRAINTS.unify(node.frame().type_environment.locals[first_target.name],
                           node.value.type_constraints.type)
    node.type_constraints = TypeInfo(NoType)


def set_return_type_constraints(node):
    t = node.value.type_constraints.type
    TYPE_CONSTRAINTS.unify(node.frame().type_environment.locals['return'], t)
    node.type_constraints = TypeInfo(NoType)


def set_functiondef_type_constraints(node):
    arg_types = [TYPE_CONSTRAINTS.lookup_concrete(node.type_environment.locals[arg])
                 for arg in node.argnames()]
    rtype = TYPE_CONSTRAINTS.lookup_concrete(node.type_environment.locals['return'])
    func_type = Callable[arg_types, rtype]
    func_type.polymorphic_tvars = [arg for arg in arg_types
                                   if isinstance(arg, TypeVar)]
    TYPE_CONSTRAINTS.unify(node.parent.frame().type_environment.locals[node.name], func_type)
    node.type_constraints = TypeInfo(NoType)


def set_call_type_constraints(node):
    try:
        func_name = node.func.name
        func_t = TYPE_CONSTRAINTS.lookup_concrete(node.frame().type_environment.locals[func_name])
    except AttributeError:
        node.type_constraints = TypeInfo(NoType)
        return

    arg_types = [arg.type_constraints.type for arg in node.args]
    ret_type = TYPE_CONSTRAINTS.unify_call(func_t, *arg_types)
    node.type_constraints = TypeInfo(ret_type)


def set_module_type_constraints(node):
    node.type_constraints = TypeInfo(NoType)
    print('All sets:', TYPE_CONSTRAINTS._sets)
    print('Global bindings:', {k: TYPE_CONSTRAINTS.lookup_concrete(t) for k, t in node.type_environment.locals.items()})


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
    type_visitor.register_transform(astroid.Return,
                                    set_return_type_constraints)
    type_visitor.register_transform(astroid.FunctionDef,
                                    set_functiondef_type_constraints)
    type_visitor.register_transform(astroid.Call,
                                    set_call_type_constraints)
    type_visitor.register_transform(astroid.Module,
                                    set_module_type_constraints)
    return type_visitor


def _set_locals_environment(node):
    node.type_environment = Environment(locals_={name: TYPE_CONSTRAINTS.fresh_tvar() for name in node.locals})
    if isinstance(node, astroid.FunctionDef):
        node.type_environment.locals['return'] = TYPE_CONSTRAINTS.fresh_tvar()


def environment_transformer() -> TransformVisitor:
    """Return a TransformVisitor that sets an environment for every node."""
    visitor = TransformVisitor()

    visitor.register_transform(astroid.FunctionDef, _set_locals_environment)
    visitor.register_transform(astroid.Module, _set_locals_environment)
    return visitor
