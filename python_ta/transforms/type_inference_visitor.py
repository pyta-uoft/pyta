import astroid.inference
import astroid
from astroid.node_classes import *
from typing import *
import typing
from typing import CallableMeta, TupleMeta, Union, _ForwardRef
from astroid.transforms import TransformVisitor
from ..typecheck.base import Environment, TypeConstraints, TypeInferenceError, parse_annotations, create_Callable,_node_to_type
from ..typecheck.errors import BINOP_TO_METHOD, UNARY_TO_METHOD, binop_error_message, unaryop_error_message
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
        visitor.register_transform(astroid.ClassDef, self._set_classdef_environment)
        visitor.register_transform(astroid.Module, self._set_module_environment)
        visitor.register_transform(astroid.ListComp, self._set_listcomp_environment)
        visitor.register_transform(astroid.DictComp, self._set_dictcomp_environment)
        visitor.register_transform(astroid.SetComp, self._set_setcomp_environment)
        return visitor

    def _set_module_environment(self, node: astroid.Module) -> None:
        """Method to set environment of a Module node."""
        node.type_environment = Environment(
            globals_={name: self.type_constraints.fresh_tvar(node)
                      for name in node.globals})
        self._populate_local_env(node)

    def _set_classdef_environment(self, node):
        """Method to set environment of a ClassDef node."""
        node.type_environment = Environment()
        for name in node.instance_attrs:
            node.type_environment.locals[name] = self.type_constraints.fresh_tvar(node)
        for name in node.locals:
            node.type_environment.locals[name] = self.type_constraints.fresh_tvar(node)

    def _set_function_def_environment(self, node):
        """Method to set environment of a FunctionDef node."""
        node.type_environment = Environment()
        # self is a special case
        if node.args.args and node.args.args[0].name == 'self' and isinstance(node.parent, astroid.ClassDef):
            node.type_environment.locals['self'] = _ForwardRef(node.parent.name)
        self._populate_local_env(node)
        node.type_environment.locals['return'] = self.type_constraints.fresh_tvar(node)

    def _set_listcomp_environment(self, node):
        """Set the environment of a ListComp node representing a list
        comprehension expression."""
        node.type_environment = Environment()
        for name in node.locals:
            node.type_environment.locals[name] = self.type_constraints.fresh_tvar(node)

    def _set_dictcomp_environment(self, node):
        """Environment setter for DictComp node representing a dictionary
        comprehension expression."""
        node.type_environment = Environment()
        for name in node.locals:
            node.type_environment.locals[name] = self.type_constraints.fresh_tvar(node)

    def _set_setcomp_environment(self, node):
        """Environment setter for SetComp node representing a set comprehension expression"""
        node.type_environment = Environment()
        for name in node.locals:
            node.type_environment.locals[name] = self.type_constraints.fresh_tvar(node)

    def _populate_local_env(self, node):
        """Helper to populate locals attributes in type environment of given node."""
        for var_name in node.locals:
            try:
                var_value = node.type_environment.lookup_in_env(var_name)
            except KeyError:
                var_value = self.type_constraints.fresh_tvar(node)
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
    def visit_const(self, node: astroid.Const) -> None:
        node.type_constraints = TypeInfo(type(node.value))

    def visit_list(self, node: astroid.List) -> None:
        if node.ctx == astroid.Store:
            # List is the target of an assignment; do not give it a type.
            node.type_constraints = TypeInfo(NoType)
        elif node.elts == []:
            node.type_constraints = TypeInfo(List[Any])
        else:
            node_type = node.elts[0].type_constraints.type
            for elt in node.elts:
                node_type = self.type_constraints.least_general_unifier(elt.type_constraints.type, node_type)
            node.type_constraints = TypeInfo(List[node_type])

    def visit_set(self, node: astroid.Set) -> None:
        if node.elts == []:
            node.type_constraints = TypeInfo(Set[Any])
        else:
            node_type = node.elts[0].type_constraints.type
            for elt in node.elts:
                node_type = self.type_constraints.least_general_unifier(elt.type_constraints.type, node_type)
            node.type_constraints = TypeInfo(Set[node_type])

    def visit_dict(self, node: astroid.Dict) -> None:
        if node.items == []:
            node.type_constraints = TypeInfo(Dict[Any, Any])
        else:
            key_type, val_type = node.items[0][0].type_constraints.type, node.items[0][1].type_constraints.type
            for key_node, val_node in node.items:
                key_type = self.type_constraints.least_general_unifier(key_node.type_constraints.type, key_type)
                val_type = self.type_constraints.least_general_unifier(val_node.type_constraints.type, val_type)
            node.type_constraints = TypeInfo(Dict[key_type, val_type])

    def visit_tuple(self, node):
        if node.ctx == astroid.Store:
            # Tuple is the target of an assignment; do not give it a type.
            node.type_constraints = TypeInfo(NoType)
        else:
            node.type_constraints = TypeInfo(
                Tuple[tuple(x.type_constraints.type for x in node.elts)])

    def visit_index(self, node):
        node.type_constraints = node.value.type_constraints

    def visit_slice(self, node):
        node.type_constraints = TypeInfo(slice)

    def visit_expr(self, node):
        """Expr nodes take the type of their child
        """
        node.type_constraints = node.value.type_constraints

    def _closest_frame(self, node, name):
        """Helper method to find the closest ancestor node containing name relative to the given node."""
        closest_scope = node
        if hasattr(closest_scope, 'type_environment') and (
                        name in closest_scope.type_environment.locals or
                        name in closest_scope.type_environment.globals or
                        name in closest_scope.type_environment.nonlocals):
            return closest_scope
        if node.parent:
            closest_scope = node.parent
            if hasattr(closest_scope, 'type_environment') and (
                            name in closest_scope.type_environment.locals or
                            name in closest_scope.type_environment.globals or
                            name in closest_scope.type_environment.nonlocals):
                return closest_scope
            else:
                return self._closest_frame(closest_scope, name)
        else:
            return closest_scope

    ##############################################################################
    # Name lookup and assignment
    ##############################################################################
    def visit_name(self, node: astroid.Name) -> None:
        try:
            node.type_constraints = TypeInfo(self.lookup_type(node, node.name))
        except KeyError:
            if node.name in self.type_store.classes:
                node.type_constraints = TypeInfo(Type[__builtins__[node.name]])
            elif node.name in self.type_store.functions:
                node.type_constraints = TypeInfo(self.type_store.functions[node.name][0])
            else:
                # This is an unbound identifier. Ignore it.
                node.type_constraints = TypeInfo(Any)

    def visit_assign(self, node: astroid.Assign) -> None:
        """Update the enclosing scope's type environment for the assignment's binding(s)."""
        # the type of the expression being assigned
        expr_type = node.value.type_constraints.type

        for target in node.targets:
            self._assign_type(target, expr_type)

        node.type_constraints = TypeInfo(NoType)

    def _assign_type(self, target: NodeNG, expr_type: type) -> None:
        """Update the type environment so that the target is bound to the given type."""
        if isinstance(target, astroid.AssignName):
            # A single identifier, e.g. x = ...
            target_type_var = self.lookup_type(target, target.name)
            self.type_constraints.unify(target_type_var, expr_type)
        elif isinstance(target, astroid.AssignAttr):
            # Attribute mutation, e.g. x.y = ...
            attr_type = self._lookup_attribute_type(target, target.expr.name, target.attrname)
            self.type_constraints.unify(attr_type, expr_type)
        elif isinstance(target, astroid.Tuple):
            # Unpacking assignment, e.g. x, y = ...
            if isinstance(expr_type, typing.TupleMeta):
                # TODO: handle when these collections are different lengths.
                for subtarget, subtype in zip(target.elts, expr_type.__args__):
                    target_tvar = self.lookup_type(subtarget, subtarget.name)
                    self.type_constraints.unify(target_tvar, subtype)
            else:
                rtype = self._handle_call(target, '__iter__', expr_type).type
                for subtarget in target.elts:
                    target_tvar = self.lookup_type(subtarget, subtarget.name)
                    self.type_constraints.unify(target_tvar, rtype.__args__[0])

    def _lookup_attribute_type(self, node, instance_name, attribute_name):
        """Given the node, class name and attribute name, return the type of the attribute."""
        class_type = self.lookup_type(node, instance_name)
        class_name = class_type.__forward_arg__
        class_env = self._closest_frame(node, class_name).locals[class_name][0].type_environment
        return self.type_constraints.lookup_concrete(class_env.lookup_in_env(attribute_name))

    def lookup_type(self, node, name):
        """Given a variable name, return its concrete type in the closest scope relative to given node."""
        tvar = self._closest_frame(node, name).type_environment.lookup_in_env(name)
        return self.type_constraints.lookup_concrete(tvar)


    ##############################################################################
    # Operation nodes
    ##############################################################################
    def visit_call(self, node: astroid.Call) -> None:
        callable_t = node.func.type_constraints.type
        if not isinstance(callable_t, (CallableMeta, list)):
            func_name = callable_t.__args__[0].__name__
            init_types = self.type_store.classes[func_name]['__init__']
            init_type = init_types[0]  # TODO: handle method overloading (through optional parameters)
            arg_types = [callable_t.__args__[0]] + [arg.type_constraints.type for arg in node.args]
            self.type_constraints.unify_call(init_type, *arg_types)
            node.type_constraints = TypeInfo(callable_t.__args__[0])
        else:
            # TODO: resolve this case (from method lookup) more gracefully
            if isinstance(callable_t, list):
                callable_t = callable_t[0]
                arg_types = [node.func.expr.type_constraints.type]
            else:
                arg_types = []
            arg_types += [arg.type_constraints.type for arg in node.args]
            ret_type = self.type_constraints.unify_call(callable_t, *arg_types, node=node)
            node.type_constraints = TypeInfo(ret_type)

    def visit_binop(self, node: astroid.BinOp) -> None:
        method_name = BINOP_TO_METHOD[node.op]
        arg_types = [node.left.type_constraints.type, node.right.type_constraints.type]
        node.type_constraints = self._handle_call(node, method_name, *arg_types, error_func=binop_error_message)

    def visit_unaryop(self, node: astroid.UnaryOp) -> None:
        # 'not' is not a function, so this handled as a separate case.
        if node.op == 'not':
            node.type_constraints = TypeInfo(bool)
        else:
            method_name = UNARY_TO_METHOD[node.op]
            node.type_constraints = self._handle_call(node, method_name, node.operand.type_constraints.type, error_func=unaryop_error_message)

    def _handle_call(self, node: NodeNG, function_name: str, *arg_types: List[type],
                     error_func: Optional[Callable[[NodeNG], str]] = None) -> TypeInfo:
        """Helper to lookup a function and unify it with given arguments.
           Return the return type of unified function call.
        """
        arg_types = [self.type_constraints.lookup_concrete(arg) for arg in arg_types]

        try:
            func_type = self.type_store.lookup_method(function_name, *arg_types)
        except KeyError:
            # No match.
            if error_func is None:
                return TypeInfo(TypeErrorInfo(f'Function {function_name} not found with given args: {arg_types}', node))
            else:
                return TypeInfo(TypeErrorInfo(error_func(node), node=node))

        try:
            return TypeInfo(self.type_constraints.unify_call(func_type, *arg_types, node=node))
        except TypeInferenceError:
            return TypeInfo(
                TypeErrorInfo('Bad unify_call of function {function_name} given args: {arg_types}', node))

    def visit_subscript(self, node):
        if hasattr(node.value, 'type_constraints') and hasattr(node.slice, 'type_constraints'):
            node.type_constraints = self._handle_call(node, '__getitem__', node.value.type_constraints.type,
                                                      node.slice.type_constraints.type)

    def visit_boolop(self, node):
        """Boolean operators are 'and', 'or'; the result type can be either of the argument types."""
        node_type_constraints = {operand_node.type_constraints.type for operand_node in node.values}
        if len(node_type_constraints) == 1:
            node.type_constraints = TypeInfo(node_type_constraints.pop())
        else:
            node.type_constraints = TypeInfo(Any)

    def visit_compare(self, node):
        """Comparison operators are: '<', '>', '==', '<=', '>=', '!=', 'in', 'is'.
        All comparisons yield boolean values."""
        # TODO: 'in' comparator
        return_types = set()
        left_value = node.left
        for comparator, right_value in node.ops:
            if comparator == 'is':
                return_types.add(bool)
            else:
                function_type = self.type_store.lookup_function(BINOP_TO_METHOD[comparator],
                                                            left_value.type_constraints.type,
                                                            right_value.type_constraints.type)
                left_value = right_value
                return_types.add(self.type_constraints.unify_call(function_type, left_value.type_constraints.type,
                                                              right_value.type_constraints.type, node=node))
        if len(return_types) == 1:
            node.type_constraints = TypeInfo(return_types.pop())
        else:
            node.type_constraints = TypeInfo(Any)

    ##############################################################################
    # Statements
    ##############################################################################
    def visit_return(self, node):
        t = node.value.type_constraints.type
        self.type_constraints.unify(node.frame().type_environment.locals['return'], t)
        node.type_constraints = TypeInfo(NoType)

    def visit_functiondef(self, node):
        arg_types = [self.lookup_type(node, arg) for arg in node.argnames()]
        if any(annotation is not None for annotation in node.args.annotations):
            func_type = parse_annotations(node)
            for arg_type, annotation in zip(arg_types, func_type.__args__[:-1]):
                self.type_constraints.unify(arg_type, annotation)
            self.type_constraints.unify(self.lookup_type(node.parent, node.name), func_type)
        else:
            # Check whether this is a method in a class
            if isinstance(node.parent, astroid.ClassDef) and isinstance(arg_types[0], TypeVar):
                self.type_constraints.unify(arg_types[0], _ForwardRef(node.parent.name), node)

            # check if return nodes exist; there is a return statement in function body.
            polymorphic_tvars = [arg for arg in arg_types if isinstance(arg, TypeVar)]
            if len(list(node.nodes_of_class(astroid.Return))) == 0:
                func_type = create_Callable(arg_types, None, polymorphic_tvars)
            else:
                rtype = self.type_constraints.lookup_concrete(node.type_environment.lookup_in_env('return'))
                func_type = create_Callable(arg_types, rtype, polymorphic_tvars)
            self.type_constraints.unify(self.lookup_type(node.parent, node.name), func_type)
        node.type_constraints = TypeInfo(NoType)

    def visit_for(self, node):
        for_node = list(node.nodes_of_class(astroid.For))[0]
        rtype = self._handle_call(node, '__iter__', for_node.iter.type_constraints.type).type
        # there may be one target, or a Generic of targets to unify.
        if isinstance(for_node.target, astroid.AssignName):
            self.type_constraints.unify(rtype.__args__[0], node.frame().type_environment.lookup_in_env(for_node.target.name))
        else:
            target_tvars = [node.frame().type_environment.lookup_in_env(target_node.name) for target_node in for_node.target.elts]
            for i in range(len(target_tvars)):
                self.type_constraints.unify(rtype.__args__[0], target_tvars[i])

    def visit_ifexp(self, node):
        if self.type_constraints.can_unify(node.body.type_constraints.type, node.orelse.type_constraints.type):
            self.type_constraints.unify(node.body.type_constraints.type, node.orelse.type_constraints.type)
            node.type_constraints = TypeInfo(node.body.type_constraints.type)
        else:
            node.type_constraints = TypeInfo(Any)

    def visit_comprehension(self, node):
        arg_type = self.type_constraints.lookup_concrete(node.iter.type_constraints.type)
        rtype = self._handle_call(node, '__iter__', arg_type).type
        if isinstance(node.target, astroid.Tuple):
            for target_node in node.target.elts:
                self.type_constraints.unify(self.lookup_type(target_node, target_node.name), rtype, node)
        else:
            self.type_constraints.unify(self.lookup_type(node.target, node.target.name), rtype.__args__[0])
        node.type_constraints = TypeInfo(NoType)

    def visit_listcomp(self, node):
        val_type = self.type_constraints.lookup_concrete(node.elt.type_constraints.type)
        node.type_constraints = TypeInfo(List[val_type])

    def visit_dictcomp(self, node):
        key_type = self.type_constraints.lookup_concrete(node.key.type_constraints.type)
        val_type = self.type_constraints.lookup_concrete(node.value.type_constraints.type)
        node.type_constraints = TypeInfo(Dict[key_type, val_type])

    def visit_setcomp(self, node):
        elt_type = self.type_constraints.lookup_concrete(node.elt.type_constraints.type)
        node.type_constraints = TypeInfo(Set[elt_type])

    def visit_classdef(self, node):
        node.type_constraints = TypeInfo(NoType)

    def visit_attribute(self, node: astroid.Attribute) -> None:
        expr_type = node.expr.type_constraints.type
        if expr_type.__name__ not in self.type_store.classes:
            raise TypeInferenceError('Invalid type')
        else:
            attribute_type = self.type_store.classes[expr_type.__name__].get(node.attrname)
            if attribute_type is None:
                raise TypeInferenceError(f'Attribute {node.attrname} not found for type {expr_type.__name__}')
            else:
                node.type_constraints = TypeInfo(attribute_type)

    def visit_annassign(self, node):
        variable_type = self.type_constraints.lookup_concrete(
            self._closest_frame(node, node.target.name).type_environment.lookup_in_env(node.target.name))
        self.type_constraints.unify(variable_type, _node_to_type(node.annotation.name))
        node.type_constraints = TypeInfo(NoType)

    def visit_module(self, node):
        node.type_constraints = TypeInfo(NoType)
        # print('All sets:', self.type_constraints._sets)
        # print('Global bindings:', {k: self.type_constraints.lookup_concrete(t) for k, t in node.type_environment.locals.items()})

