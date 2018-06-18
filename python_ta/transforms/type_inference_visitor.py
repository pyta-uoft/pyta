import astroid.inference
import astroid
from astroid.node_classes import *
from typing import *
import typing
from typing import CallableMeta, TupleMeta, Union, _ForwardRef
from astroid.transforms import TransformVisitor
from ..typecheck.base import Environment, TypeConstraints, parse_annotations, \
    create_Callable,_node_to_type, TypeResult, TypeInfo, TypeFail, failable_collect, accept_failable
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


class TypeInferer:
    """The class responsible for inferring types given an astroid AST.
    """
    type_constraints = TypeConstraints()
    type_store = TypeStore(type_constraints)

    def __init__(self):
        self.type_constraints.reset()

    def reset(self):
        self.type_store = TypeStore(self.type_constraints)

    ###########################################################################
    # Setting up the environment
    ###########################################################################
    def environment_transformer(self) -> TransformVisitor:
        """Return a TransformVisitor that sets an environment for every node."""
        visitor = TransformVisitor()
        visitor.register_transform(astroid.FunctionDef, self._set_function_def_environment)
        visitor.register_transform(astroid.ClassDef, self._set_classdef_environment)
        visitor.register_transform(astroid.Module, self._set_module_environment)
        visitor.register_transform(astroid.ListComp, self._set_comprehension_environment)
        visitor.register_transform(astroid.DictComp, self._set_comprehension_environment)
        visitor.register_transform(astroid.SetComp, self._set_comprehension_environment)
        visitor.register_transform(astroid.GeneratorExp, self._set_comprehension_environment)
        return visitor

    def _set_module_environment(self, node: astroid.Module) -> None:
        """Method to set environment of a Module node."""
        node.type_environment = Environment(
            globals_={name: self.type_constraints.fresh_tvar(node.globals[name][0])
                      for name in node.globals})
        self._populate_local_env(node)

    def _set_classdef_environment(self, node):
        """Method to set environment of a ClassDef node."""
        node.type_environment = Environment()
        for name in node.instance_attrs:
            node.type_environment.locals[name] = self.type_constraints.fresh_tvar(node.instance_attrs[name][0])
            self.type_store.classes[node.name][name] = [node.type_environment.locals[name]]
        for name in node.locals:
            node.type_environment.locals[name] = self.type_constraints.fresh_tvar(node.locals[name][0])

    def _set_function_def_environment(self, node):
        """Method to set environment of a FunctionDef node."""
        node.type_environment = Environment()
        # self is a special case
        if node.args.args and node.args.args[0].name == 'self' and isinstance(node.parent, astroid.ClassDef):
            node.type_environment.locals['self'] = _ForwardRef(node.parent.name)
        self._populate_local_env(node)
        node.type_environment.locals['return'] = self.type_constraints.fresh_tvar(node)

    def _set_comprehension_environment(self, node):
        """Set the environment of a comprehension expression.

        Covers ListComp, SetComp, DictComp, and GeneratorExp."""
        node.type_environment = Environment()
        for name in node.locals:
            node.type_environment.locals[name] = self.type_constraints.fresh_tvar(node)

    def _populate_local_env(self, node):
        """Helper to populate locals attributes in type environment of given node."""
        for var_name in node.locals:
            try:
                var_value = node.type_environment.lookup_in_env(var_name)
            except KeyError:
                var_value = self.type_constraints.fresh_tvar(node.locals[var_name][0])
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
        node.inf_type = TypeInfo(type(node.value))

    def visit_list(self, node: astroid.List) -> None:
        if node.ctx == astroid.Store:
            # List is the target of an assignment; do not give it a type.
            node.inf_type = TypeInfo(NoType)
        elif not node.elts:
            node.inf_type = TypeInfo(List[Any])
        else:
            elt_inf_type = self.unify_elements(node.elts, node)
            node.inf_type = self.wrap_container(List, elt_inf_type)

    def visit_set(self, node: astroid.Set) -> None:
        if not node.elts:
            node.inf_type = TypeInfo(Set[Any])
        else:
            elt_inf_type = self.unify_elements(node.elts, node)
            node.inf_type = self.wrap_container(Set, elt_inf_type)

    def visit_dict(self, node: astroid.Dict) -> None:
        if not node.items:
            node.inf_type = TypeInfo(Dict[Any, Any])
        else:
            key_list, val_list = zip(*node.items)
            key_inf_type = self.unify_elements(key_list, node)
            val_inf_type = self.unify_elements(val_list, node)
            node.inf_type = self.wrap_container(Dict, key_inf_type, val_inf_type)

    def visit_tuple(self, node):
        if node.ctx == astroid.Store:
            # Tuple is the target of an assignment; do not give it a type.
            node.inf_type = TypeInfo(NoType)
        else:
            node.inf_type = self.wrap_container(Tuple, *(e.inf_type for e in node.elts))

    def unify_elements(self, lst: List[NodeNG], node: NodeNG) -> TypeInfo:
        lst = list(lst)
        elt_inf_type = lst[0].inf_type
        for cur_elt in lst:
            elt_inf_type = self.type_constraints.unify(elt_inf_type, cur_elt.inf_type, node)
        if isinstance(elt_inf_type, TypeFail):
            return TypeInfo(Any)
        return elt_inf_type

    @accept_failable
    def wrap_container(self, container_type: GenericMeta, *args: List[type]) -> TypeInfo:
        return TypeInfo(container_type[tuple(args)])

    ##############################################################################
    # Expression types
    ##############################################################################
    def visit_ifexp(self, node: astroid.IfExp) -> None:
        node.inf_type = self.type_constraints.unify(node.body.inf_type, node.orelse.inf_type, node)

    def visit_expr(self, node):
        """Expr nodes take the type of their child
        """
        node.inf_type = node.value.inf_type

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
            node.inf_type = TypeInfo(self.lookup_type(node, node.name))
        except KeyError:
            if node.name in self.type_store.classes:
                node.inf_type = TypeInfo(Type[__builtins__[node.name]])
            elif node.name in self.type_store.functions:
                node.inf_type = TypeInfo(self.type_store.functions[node.name][0])
            else:
                # This is an unbound identifier. Ignore it.
                node.inf_type = TypeInfo(Any)

    def visit_assign(self, node: astroid.Assign) -> None:
        """Update the enclosing scope's type environment for the assignment's binding(s)."""
        # the type of the expression being assigned
        if isinstance(node.value, astroid.Name):
            expr_inf_type = TypeInfo(self.lookup_typevar(node, node.value.name))
        else:
            expr_inf_type = node.value.inf_type

        node.inf_type = TypeInfo(NoType)

        for target in node.targets:
            type_result = self._assign_type(target, expr_inf_type, node)
            if isinstance(type_result, TypeFail):
                node.inf_type = type_result

    @accept_failable
    def _assign_type(self, target: NodeNG, expr_type: type, node: astroid.Assign) -> TypeResult:
        """Update the type environment so that the target is bound to the given type."""
        if isinstance(target, astroid.AssignName):
            # A single identifier, e.g. x = ...
            target_type_var = self.lookup_type(target, target.name)
            return self.type_constraints.unify(target_type_var, expr_type, node)
        elif isinstance(target, astroid.AssignAttr):
            # Attribute mutation, e.g. x.y = ...
            attr_type = self._lookup_attribute_type(target, target.expr.name, target.attrname)
            return self.type_constraints.unify(attr_type, expr_type, node)
        elif isinstance(target, astroid.Tuple):
            # Unpacking assignment, e.g. x, y = ...
            if isinstance(expr_type, typing.TupleMeta):
                return self.type_constraints.unify(
                    Tuple[tuple(self.lookup_type(subtarget, subtarget.name) for subtarget in target.elts)],
                    expr_type, node
                )
            else:
                iter_type_result = self._handle_call(target, '__iter__', expr_type)
                for subtarget in target.elts:
                    target_tvar = self.lookup_type(subtarget, subtarget.name)
                    iter_type_result >> (
                        lambda t: self.type_constraints.unify(target_tvar, t.__args__[0], node)
                    )
                return iter_type_result
        elif isinstance(target, astroid.Subscript):
            # TODO: previous case must recursively handle this one
            return self._handle_call(target, '__setitem__', target.value.inf_type, target.slice.inf_type, expr_type)

    def _lookup_attribute_type(self, node, instance_name, attribute_name):
        """Given the node, class name and attribute name, return the type of the attribute."""
        class_type = self.lookup_type(node, instance_name)
        class_name = class_type.__forward_arg__
        class_env = self._closest_frame(node, class_name).locals[class_name][0].type_environment
        return self.type_constraints.resolve(class_env.lookup_in_env(attribute_name)).getValue()

    def lookup_type(self, node, name):
        """Given a variable name, return its concrete type in the closest scope relative to given node."""
        tvar = self._closest_frame(node, name).type_environment.lookup_in_env(name)
        return self.type_constraints.resolve(tvar).getValue()

    def lookup_typevar(self, node: NodeNG, name: str):
        return self._closest_frame(node, name).type_environment.lookup_in_env(name)

    ##############################################################################
    # Operation nodes
    ##############################################################################
    def visit_call(self, node: astroid.Call) -> None:
        callable_t = node.func.inf_type.getValue()
        is_union = hasattr(callable_t, '__origin__') and callable_t.__origin__ is Union

        # case when callable_t is the type of a class
        if hasattr(callable_t, '__name__') and callable_t.__name__ == 'Type':
            callable_t = callable_t.__args__[0]

        if not isinstance(callable_t, (CallableMeta, list)) and not is_union:
            if isinstance(callable_t, _ForwardRef):
                func_name = callable_t.__forward_arg__
            else:
                func_name = callable_t.__args__[0].__name__
            if '__init__' in self.type_store.classes[func_name]:
                init_type = self.type_store.classes[func_name]['__init__'][0]
            else:
                init_type = Callable[[callable_t], None]
            # TODO: handle method overloading (through optional parameters)
            arg_types = [callable_t] + [arg.inf_type.getValue() for arg in node.args]
            # TODO: Check for number of arguments if function is an initializer
            type_result = self.type_constraints.unify_call(init_type, *arg_types, node=node)
            if isinstance(type_result, TypeFail):
                node.inf_type = type_result
            else:
                node.inf_type = TypeInfo(callable_t)
        else:
            # TODO: resolve this case (from method lookup) more gracefully
            if isinstance(callable_t, list):
                callable_t = callable_t[0]
                arg_types = [node.func.expr.inf_type.getValue()]
            else:
                arg_types = []
            arg_types += [arg.inf_type.getValue() for arg in node.args]
            node.inf_type = self.type_constraints.unify_call(callable_t, *arg_types, node=node)

    def visit_binop(self, node: astroid.BinOp) -> None:
        method_name = BINOP_TO_METHOD[node.op]
        node.inf_type = self._handle_call(node, method_name, node.left.inf_type, node.right.inf_type, error_func=binop_error_message)

    def visit_unaryop(self, node: astroid.UnaryOp) -> None:
        # 'not' is not a function, so this handled as a separate case.
        if node.op == 'not':
            node.inf_type = TypeInfo(bool)
        else:
            method_name = UNARY_TO_METHOD[node.op]
            node.inf_type = self._handle_call(node, method_name, node.operand.inf_type, error_func=unaryop_error_message)

    def visit_boolop(self, node: astroid.BoolOp) -> None:
        node.inf_type = self.unify_elements(node.values, node)
        if isinstance(node.inf_type, TypeFail):
            node.inf_type = TypeInfo(Any)

    def visit_compare(self, node: astroid.Compare) -> None:
        return_types = set()
        left = node.left
        for comparator, right in node.ops:
            if comparator == 'is':
                return_types.add(bool)
            elif comparator == 'in':
                resolved_type = self._handle_call(
                    node,
                    BINOP_TO_METHOD[comparator],
                    right.inf_type,
                    left.inf_type
                )
                if isinstance(resolved_type, TypeFail):
                    node.inf_type = resolved_type
                    return
                resolved_type >> return_types.add
            else:
                resolved_type = self._handle_call(
                    node,
                    BINOP_TO_METHOD[comparator],
                    left.inf_type,
                    right.inf_type
                )
                if isinstance(resolved_type, TypeFail):
                    node.inf_type = resolved_type
                    return
                resolved_type >> return_types.add
        if len(return_types) == 1:
            node.inf_type = TypeInfo(return_types.pop())
        else:
            node.inf_type = TypeInfo(Any)

    ##############################################################################
    # Subscripting
    ##############################################################################
    def visit_index(self, node: astroid.Index) -> None:
        node.inf_type = node.value.inf_type

    def visit_slice(self, node: astroid.Slice) -> None:
        lower_type = node.lower.inf_type.getValue() if node.lower else type(None)
        upper_type = node.upper.inf_type.getValue() if node.upper else type(None)
        step_type = node.step.inf_type.getValue() if node.step else type(None)
        node.inf_type = self._handle_call(node, '__init__', slice, lower_type,
                                          upper_type, step_type)
        if node.inf_type.getValue() == type(None):
            node.inf_type = TypeInfo(slice)

    def visit_extslice(self, node: astroid.ExtSlice):
        unif_res = failable_collect([dim.inf_type for dim in node.dims])
        if isinstance(unif_res, TypeFail):
            return unif_res
        node.inf_type = TypeInfo(Tuple[tuple(unif_res.getValue())])

    def visit_subscript(self, node: astroid.Subscript) -> None:
        if isinstance(node.slice.inf_type, TypeFail):
            node.inf_type = node.slice.inf_type
        elif node.ctx == astroid.Load:
            node.inf_type = self._handle_call(node, '__getitem__', node.value.inf_type, node.slice.inf_type)
        elif node.ctx == astroid.Store:
            node.inf_type = TypeInfo(NoType)
        elif node.ctx == astroid.Del:
            node.inf_type = self._handle_call(node, '__delitem__', node.value.inf_type, node.slice.inf_type)

    ##############################################################################
    # Loops
    ##############################################################################
    def visit_for(self, node):
        iter_type_result = self._handle_call(node, '__iter__', node.iter.inf_type)
        if isinstance(node.target, astroid.AssignName):
            target_type = self.lookup_type(node.target, node.target.name)
        else:
            target_type = Tuple[tuple(self.lookup_type(subtarget, subtarget.name) for subtarget in node.target.elts)]
        iter_type_result >> (
            lambda t: self.type_constraints.unify(t.__args__[0], target_type, node))
        node.inf_type = iter_type_result if isinstance(iter_type_result, TypeFail) else TypeInfo(NoType)

    ##############################################################################
    # Comprehensions
    ##############################################################################
    def visit_comprehension(self, node: astroid.Comprehension) -> None:
        self.visit_for(node)

    def visit_dictcomp(self, node: astroid.DictComp) -> None:
        key_inf_type = self.type_constraints.resolve(node.key.inf_type)
        val_inf_type = self.type_constraints.resolve(node.value.inf_type)
        node.inf_type = self.wrap_container(Dict, key_inf_type, val_inf_type)

    def visit_generatorexp(self, node: astroid.GeneratorExp) -> None:
        elt_inf_type = self.type_constraints.resolve(node.elt.inf_type)
        node.inf_type = self.wrap_container(Generator, elt_inf_type, None, None)

    def visit_listcomp(self, node: astroid.ListComp) -> None:
        val_inf_type = self.type_constraints.resolve(node.elt.inf_type)
        node.inf_type = self.wrap_container(List, val_inf_type)

    def visit_setcomp(self, node: astroid.SetComp) -> None:
        elt_inf_type = self.type_constraints.resolve(node.elt.inf_type)
        node.inf_type = self.wrap_container(Set, elt_inf_type)

    @accept_failable
    def _handle_call(self, node: NodeNG, function_name: str, *arg_types: List[type],
                     error_func: Optional[Callable[[NodeNG], str]] = None) -> TypeResult:
        """Helper to lookup a function and unify it with given arguments.
           Return the return type of unified function call.
        """
        arg_types = [self.type_constraints.resolve(arg).getValue() for arg in arg_types]

        try:
            func_type = self.type_store.lookup_method(function_name, *arg_types)
        except KeyError as e:
            # No match.
            if error_func is None:
                return TypeFail(f'Function {function_name} not found with given args: {arg_types}')
            else:
                return TypeFail(error_func(node))
        return self.type_constraints.unify_call(func_type, *arg_types, node=node)

    ##############################################################################
    # Definitions
    ##############################################################################
    def visit_functiondef(self, node: astroid.FunctionDef) -> None:
        node.inf_type = TypeInfo(NoType)

        # Get the inferred type of the function.
        inferred_args = [self.lookup_type(node, arg) for arg in node.argnames()]

        if isinstance(node.parent, astroid.ClassDef) and isinstance(inferred_args[0], TypeVar):
            # first argument is special in these cases
            if node.type == 'method':
                self.type_constraints.unify(inferred_args[0], _ForwardRef(node.parent.name), node)
            elif node.type == 'classmethod':
                self.type_constraints.unify(inferred_args[0], Type[_ForwardRef(node.parent.name)], node)

        if any(node.nodes_of_class(astroid.Return)):
            inferred_return = self.type_constraints.resolve(node.type_environment.lookup_in_env('return')).getValue()
        elif node.name == '__init__':
            inferred_return = inferred_args[0]
        else:
            inferred_return = type(None)

        # Get any function type annotations.
        if any(annotation is not None for annotation in node.args.annotations):
            annotated_type = parse_annotations(node)
        else:
            annotated_type = None

        # Combine inferred and annotated types.
        if annotated_type:
            combined_args = []
            for inferred, annotated in zip(inferred_args, annotated_type.__args__[:-1]):
                if annotated is None:
                    annotated = type(None)
                t = self.type_constraints.unify(inferred, annotated, node).getValue()
                combined_args.append(t)

            annotated_rtype = annotated_type.__args__[-1]
            if node.name == '__init__':
                annotated_rtype = inferred_args[0]
            elif annotated_rtype is None:
                annotated_rtype = type(None)
            combined_return = self.type_constraints.unify(
                inferred_return, annotated_rtype, node).getValue()
        else:
            combined_args, combined_return = inferred_args, inferred_return

        # Update the environment storing the function's type.
        polymorphic_tvars = [arg for arg in combined_args if isinstance(arg, TypeVar)]
        func_type = create_Callable(combined_args, combined_return, polymorphic_tvars)
        num_defaults = len(node.args.defaults)
        if num_defaults > 0:
            for i in range(num_defaults):
                opt_args = inferred_args[:-1-i]
                opt_func_type = create_Callable(opt_args, combined_return, polymorphic_tvars)
                func_type = Union[func_type, opt_func_type]
        self.type_constraints.unify(
            self.lookup_type(node.parent, node.name), func_type, node)

    def visit_arguments(self, node: astroid.Arguments) -> None:
        node.inf_type = TypeInfo(NoType)
        for i in range(len(node.annotations)):
            if node.annotations[i] is not None:
                arg_tvar = self.lookup_type(node, node.args[i].name)
                self.type_constraints.unify(
                    arg_tvar, _node_to_type(node.annotations[i]), node)

    def visit_return(self, node: astroid.Return) -> None:
        val_inf_type = self.type_constraints.unify(node.value.inf_type, self.lookup_type(node, 'return'), node)
        node.inf_type = val_inf_type if isinstance(val_inf_type, TypeFail) else TypeInfo(NoType)

    def visit_classdef(self, node: astroid.ClassDef) -> None:
        node.inf_type = TypeInfo(NoType)
        self.type_constraints.unify(self.lookup_type(node.parent, node.name),
                                    _ForwardRef(node.name), node)

        # Update type_store for this class.
        # TODO: include node.instance_attrs as well?
        for attr in node.locals:
            attr_inf_type = self.type_constraints.resolve(node.type_environment.lookup_in_env(attr))
            attr_inf_type >> self.type_store.classes[node.name][attr].append
            attr_inf_type >> (
                lambda a: self.type_store.methods[attr].append(a) if isinstance(a, CallableMeta) else None)

    ##############################################################################
    # Statements
    ##############################################################################
    def visit_attribute(self, node: astroid.Attribute) -> None:
        expr_type = node.expr.inf_type.getValue()
        if isinstance(expr_type, _ForwardRef):
            type_name =  expr_type.__forward_arg__
        elif hasattr(expr_type, '__name__'):
            type_name = expr_type.__name__
        else:
            type_name = None
        if type_name not in self.type_store.classes:
            node.inf_type = TypeFail('Invalid attribute type')
        else:
            attribute_type = self.type_store.classes[type_name].get(node.attrname)
            if attribute_type is None:
                node.inf_type = TypeFail(f'Attribute {node.attrname} not found for type {type_name}')
            else:
                attribute_type = attribute_type[0]
                # Detect an instance method call, and create a bound method signature (first argument removed).
                # TODO: handle classmethod calls differently.
                if isinstance(attribute_type, CallableMeta):
                    attribute_type = Callable[list(attribute_type.__args__[1:-1]), attribute_type.__args__[-1]]
                node.inf_type = TypeInfo(attribute_type)

    def visit_annassign(self, node):
        var_inf_type = self.type_constraints.resolve(
            self._closest_frame(node, node.target.name).type_environment.lookup_in_env(node.target.name))
        self.type_constraints.unify(var_inf_type, _node_to_type(node.annotation.name), node)
        node.inf_type = TypeInfo(NoType)

    def visit_module(self, node):
        node.inf_type = TypeInfo(NoType)
        # print('All sets:', self.type_constraints._nodes)
        # print('Global bindings:', {k: self.type_constraints.resolve(t) for k, t in node.type_environment.locals.items()})


# Main function (useful for quick debugging)
def main(source: str) -> Tuple[astroid.Module, TypeInferer]:
    """Parse a string representing source text, and perform a typecheck.

    Return the astroid Module node (with the type_constraints attribute set
    on all nodes in the tree) and TypeInferer object.
    """
    module = astroid.parse(source)
    type_inferer = TypeInferer()
    type_inferer.environment_transformer().visit(module)
    type_inferer.type_inference_transformer().visit(module)
    return module, type_inferer
