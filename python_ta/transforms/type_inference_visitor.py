import astroid.inference
import astroid
from astroid.node_classes import *
from typing import *
from typing import CallableMeta, TupleMeta, Union, _gorg, _geqv
from astroid.transforms import TransformVisitor
from ..typecheck.base import op_to_dunder_binary, op_to_dunder_unary, Environment, TypeConstraints, TypeInferenceError
from ..typecheck.type_store import TypeStore


class NoType:
    pass


class TypeErrorInfo:
    """Class representing an error in type inference."""
    def __init__(self, msg, node):
        self.msg = msg
        self.node = node

    def __str__(self):
        return self.msg


class TypeInfo:
    """A class representing the inferred type of a value.

    === Instance attributes ===
    - type (Union[type, TypeErrorInfo]): type of the inferred value
    """
    def __init__(self, type_: Union[type, TypeErrorInfo]):
        self.type = type_


class TypeInferer:
    """The class responsible for inferring types given an astroid AST.
    """
    type_constraints = TypeConstraints()
    type_store = TypeStore(type_constraints)

    def __init__(self):
        self.type_constraints.clear_tvars()

    ###########################################################################
    # Setting up the environment
    ###########################################################################
    def environment_transformer(self) -> TransformVisitor:
        """Return a TransformVisitor that sets an environment for every node."""
        visitor = TransformVisitor()
        visitor.register_transform(astroid.FunctionDef, self._set_function_def_environment)
        visitor.register_transform(astroid.Module, self._set_module_environment)
        return visitor

    def _set_module_environment(self, node):
        """Method to set environment of a Module node."""
        node.type_environment = Environment(
            globals_={name: self.type_constraints.fresh_tvar() for name in node.globals})
        self._populate_local_env(node)

    def _set_function_def_environment(self, node):
        """Method to set environment of a FunctionDef node."""
        node.type_environment = Environment()
        self._populate_local_env(node)
        node.type_environment.locals['return'] = self.type_constraints.fresh_tvar()

    def _populate_local_env(self, node):
        """Helper to populate locals attributes in type environment of given node."""
        for var_name in node.locals:
            try:
                var_value = node.type_environment.lookup_in_env(var_name)
            except KeyError:
                var_value = self.type_constraints.fresh_tvar()
            node.type_environment.locals[var_name] = var_value

    ###########################################################################
    # Type inference methods
    ###########################################################################
    def type_inference_transformer(self) -> TransformVisitor:
        """Instantiate a visitor to perform type inference on an AST.
        """
        type_visitor = TransformVisitor()
        for klass in astroid.ALL_NODE_CLASSES:
            if hasattr(self, f'visit_{klass.__name__.lower()}'):
                type_visitor.register_transform(klass, getattr(self, f'visit_{klass.__name__.lower()}'))
        return type_visitor

    ##############################################################################
    # Literals
    ##############################################################################
    def visit_const(self, node):
        """Populate type constraints for astroid nodes for num/str/bool/None/bytes literals."""
        node.type_constraints = TypeInfo(type(node.value))

    def visit_tuple(self, node):
        # Tuple is being evaluated rather than assigned to - find types of its elements
        if node.ctx == astroid.Load:
            node.type_constraints = TypeInfo(
                Tuple[tuple(x.type_constraints.type for x in node.elts)])
        else:
            # Tuple is on LHS; will never have a type.
            node.type_constraints = TypeInfo(NoType)

    def visit_list(self, node):
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

    def visit_dict(self, node):
        # node_types contains types of elements inside Dict.
        key_types = {key.type_constraints.type for key, _ in node.items}
        value_types = {value.type_constraints.type for _, value in node.items}

        # If all the keys have the same type and all the values have the same type,
        # set the type constraint to a Dict of the two types.
        # Else, just use the general Dict type.
        if len(key_types) == 1 and len(value_types) == 1:
            node.type_constraints = TypeInfo(Dict[key_types.pop(), value_types.pop()])
        else:
            node.type_constraints = TypeInfo(Dict[Any, Any])

    def visit_index(self, node):
        node.type_constraints = node.value.type_constraints

    def visit_slice(self, node):
        node.type_constraints = TypeInfo(slice)

    def visit_expr(self, node):
        """Expr nodes take the type of their child
        """
        node.type_constraints = node.value.type_constraints

    def visit_name(self, node):
        try:
            node.type_constraints = TypeInfo(node.frame().type_environment.lookup_in_env(node.name))
        except KeyError:
            node.frame().type_environment.create_in_env(self.type_constraints, 'globals', node.name)
            node.type_constraints = TypeInfo(node.frame().type_environment.globals[node.name])

    ##############################################################################
    # Operation nodes
    ##############################################################################
    def visit_binop(self, node):
        t1 = self.type_constraints.lookup_concrete(node.left.type_constraints.type)
        t2 = self.type_constraints.lookup_concrete(node.right.type_constraints.type)
        op_name = op_to_dunder_binary(node.op)

        try:
            method_type = self.type_store.lookup_function(op_name, t1, t2)
        except KeyError:
            node.type_constraints = TypeInfo(
                TypeErrorInfo('Method {}.{}({}) not found'.format(t1, op_name, t2), node)
            )
            return

        try:
            return_type = self.type_constraints.unify_call(method_type, t1, t2)
        except TypeInferenceError:
            node.type_constraints = TypeInfo(
                TypeErrorInfo('incompatible types {} and {} in BinOp'.format(t1, t2), node)
            )
        else:
            node.type_constraints = TypeInfo(return_type)

    def visit_unaryop(self, node):
        if node.op == 'not':
            node.type_constraints = TypeInfo(bool)
        else:
            unary_function = self.type_store.lookup_function(op_to_dunder_unary(node.op), node.operand.type_constraints.type)
            node.type_constraints = TypeInfo(
                self.type_constraints.unify_call(unary_function, node.operand.type_constraints.type))

    def visit_subscript(self, node):
        if hasattr(node.value, 'type_constraints') and hasattr(node.slice, 'type_constraints'):
            value_type = node.value.type_constraints.type
            arg_type = node.slice.type_constraints.type
            op_name = '__getitem__'

            try:
                method_type = self.type_store.lookup_function(op_name, value_type, arg_type)
            except KeyError:
                node.type_constraints = TypeInfo(
                    TypeErrorInfo('Method {}.{} not found'.format(value_type, op_name), node)
                )
                return

            try:
                return_type = self.type_constraints.unify_call(method_type, value_type, arg_type)
            except TypeInferenceError:
                node.type_constraints = TypeInfo(
                    TypeErrorInfo('incompatible types {} and {} in Subscript'.format(value_type, arg_type), node)
                )
            else:
                node.type_constraints = TypeInfo(return_type)

    # TODO: Add check in the visit_compare as in BinOp.
    def visit_compare(self, node):
        """Compare operators includes:
        '<', '>', '==', '>=', '<=', '<>', '!=', 'is' ['not'], ['not'] 'in' """
        node.type_constraints = TypeInfo(bool)

    def visit_boolop(self, node):
        """Boolean operators are 'and', 'or'; the result type can be either of the argument types."""
        node_type_constraints = {operand_node.type_constraints.type for operand_node in node.values}
        if len(node_type_constraints) == 1:
            node.type_constraints = TypeInfo(node_type_constraints.pop())
        else:
            node.type_constraints = TypeInfo(Any)

    ##############################################################################
    # Statements
    ##############################################################################
    def visit_assign(self, node):
        # multi-assignment; LHS is a tuple of AssignName target nodes as "elements"
        if isinstance(node.targets[0], astroid.Tuple):
            target_type_tuple = zip(node.targets[0].elts, node.value.elts)
            for target_node, value in target_type_tuple:
                target_type_var = node.frame().type_environment.lookup_in_env(target_node.name)
                self.type_constraints.unify(target_type_var, value.type_constraints.type)
        else:
            # assignment(s) in single statement
            for target_node in node.targets:
                target_type_var = node.frame().type_environment.lookup_in_env(target_node.name)
                self.type_constraints.unify(target_type_var, node.value.type_constraints.type)
        node.type_constraints = TypeInfo(NoType)

    def visit_return(self, node):
        t = node.value.type_constraints.type
        self.type_constraints.unify(node.frame().type_environment.locals['return'], t)
        node.type_constraints = TypeInfo(NoType)

    def visit_functiondef(self, node):
        arg_types = [self.type_constraints.lookup_concrete(node.type_environment.lookup_in_env(arg))
                     for arg in node.argnames()]
        # check if return nodes exist; there is a return statement in function body.
        if len(list(node.nodes_of_class(astroid.Return))) == 0:
            func_type = Callable[arg_types, None]
        else:
            rtype = self.type_constraints.lookup_concrete(node.type_environment.lookup_in_env('return'))
            func_type = Callable[arg_types, rtype]
        func_type.polymorphic_tvars = [arg for arg in arg_types
                                       if isinstance(arg, TypeVar)]
        self.type_constraints.unify(node.parent.frame().type_environment.lookup_in_env(node.name), func_type)
        node.type_constraints = TypeInfo(NoType)

    def visit_call(self, node):
        try:
            func_name = node.func.name
            func_t = self.type_constraints.lookup_concrete(node.frame().type_environment.locals[func_name])
        except AttributeError:
            node.type_constraints = TypeInfo(NoType)
            return

        arg_types = [arg.type_constraints.type for arg in node.args]
        ret_type = self.type_constraints.unify_call(func_t, *arg_types)
        node.type_constraints = TypeInfo(ret_type)

    def visit_module(self, node):
        node.type_constraints = TypeInfo(NoType)
        # print('All sets:', self.type_constraints._sets)
        # print('Global bindings:', {k: self.type_constraints.lookup_concrete(t) for k, t in node.type_environment.locals.items()})
