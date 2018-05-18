import astroid.inference
import astroid
from astroid.node_classes import *
from typing import *
import typing
from typing import CallableMeta, TupleMeta, Union, _ForwardRef
from astroid.transforms import TransformVisitor
from ..typecheck.base import Environment, TypeConstraints, parse_annotations, create_Callable,_node_to_type, TypeResult, TypeInfo, TypeFail
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
            globals_={name: self.type_constraints.fresh_tvar(node)
                      for name in node.globals})
        self._populate_local_env(node)

    def _set_classdef_environment(self, node):
        """Method to set environment of a ClassDef node."""
        node.type_environment = Environment()
        for name in node.instance_attrs:
            node.type_environment.locals[name] = self.type_constraints.fresh_tvar(node)
            self.type_store.classes[node.name][name] = [node.type_environment.locals[name]]
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
        node.inf_type = TypeInfo(type(node.value))

    def visit_list(self, node: astroid.List) -> None:
        if node.ctx == astroid.Store:
            # List is the target of an assignment; do not give it a type.
            node.inf_type = TypeInfo(NoType)
        elif node.elts == []:
            node.inf_type = TypeInfo(List[Any])
        else:
            node_type = node.elts[0].inf_type.getValue()
            for elt in node.elts:
                if isinstance(node_type, type):
                    node_type = self.type_constraints.unify(elt.inf_type.getValue(), node_type).getValue()
            if isinstance(node_type, str):
                node_type = Any
            node.inf_type = TypeInfo(List[node_type])

    def visit_set(self, node: astroid.Set) -> None:
        if node.elts == []:
            node.inf_type = TypeInfo(Set[Any])
        else:
            node_type = node.elts[0].inf_type.getValue()
            for elt in node.elts:
                self.type_constraints.unify(int, None)
                if isinstance(node_type, type):
                    node_type = self.type_constraints.unify(elt.inf_type.getValue(), node_type).getValue()
            if isinstance(node_type, str):
                node_type = Any
            node.inf_type = TypeInfo(Set[node_type])

    def visit_dict(self, node: astroid.Dict) -> None:
        if node.items == []:
            node.inf_type = TypeInfo(Dict[Any, Any])
        else:
            key_type, val_type = node.items[0][0].inf_type.getValue(), node.items[0][1].inf_type.getValue()
            for key_node, val_node in node.items:
                if isinstance(key_type, type):
                    key_type = self.type_constraints.unify(key_node.inf_type.getValue(), key_type).getValue()
                if isinstance(val_type, type):
                    val_type = self.type_constraints.unify(val_node.inf_type.getValue(), val_type).getValue()
            if isinstance(key_type, str):
                key_type = Any
            if isinstance(val_type, str):
                val_type = Any
            node.inf_type = TypeInfo(Dict[key_type, val_type])

    def visit_tuple(self, node):
        if node.ctx == astroid.Store:
            # Tuple is the target of an assignment; do not give it a type.
            node.inf_type = TypeInfo(NoType)
        else:
            node.inf_type = TypeInfo(
                Tuple[tuple(x.inf_type.getValue() for x in node.elts)])

    ##############################################################################
    # Expression types
    ##############################################################################
    def visit_ifexp(self, node: astroid.IfExp) -> None:
        node.inf_type = self.type_constraints.unify(node.body.inf_type.getValue(), node.orelse.inf_type.getValue())

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
        expr_type = node.value.inf_type.getValue()
        node.inf_type = TypeInfo(NoType)

        for target in node.targets:
            self._assign_type(target, expr_type)
            if isinstance(expr_type, typing.TupleMeta) and isinstance(target, astroid.Tuple):
                if len(expr_type.__args__) > len(target.elts):
                    node.inf_type = TypeFail("Too many values in assignment node")
                elif len(expr_type.__args__) < len(target.elts):
                    node.inf_type = TypeFail("Too many variables in assignment node")
            elif isinstance(expr_type, typing.TupleMeta):
                node.inf_type = TypeFail("Cannot assign multiple values to single variable")
            elif isinstance(target, astroid.Tuple):
                node.inf_type = TypeFail("Cannot assign single value to multiple variables")

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
                self.type_constraints.unify(
                    Tuple[tuple(self.lookup_type(subtarget, subtarget.name) for subtarget in target.elts)],
                    expr_type
                )
            else:
                iter_type_result = self._handle_call(target, '__iter__', expr_type)
                if not isinstance(iter_type_result, TypeFail):
                    iter_type = iter_type_result.getValue()
                    contained_type = iter_type.__args__[0]
                    for subtarget in target.elts:
                        target_tvar = self.lookup_type(subtarget, subtarget.name)
                        self.type_constraints.unify(target_tvar, contained_type)

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


    ##############################################################################
    # Operation nodes
    ##############################################################################
    def visit_call(self, node: astroid.Call) -> None:
        callable_t = node.func.inf_type.getValue()
        if not isinstance(callable_t, (CallableMeta, list)):
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
            self.type_constraints.unify_call(init_type, *arg_types)
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
        arg_types = [node.left.inf_type.getValue(), node.right.inf_type.getValue()]
        node.inf_type = self._handle_call(node, method_name, *arg_types, error_func=binop_error_message)

    def visit_unaryop(self, node: astroid.UnaryOp) -> None:
        # 'not' is not a function, so this handled as a separate case.
        if node.op == 'not':
            node.inf_type = TypeInfo(bool)
        else:
            method_name = UNARY_TO_METHOD[node.op]
            node.inf_type = self._handle_call(node, method_name, node.operand.inf_type.getValue(), error_func=unaryop_error_message)

    def visit_boolop(self, node: astroid.BoolOp) -> None:
        node_type_constraints = {operand_node.inf_type.getValue() for operand_node in node.values}
        if len(node_type_constraints) == 1:
            node.inf_type = TypeInfo(node_type_constraints.pop())
        else:
            node.inf_type = TypeInfo(Any)

    def visit_compare(self, node: astroid.Compare) -> None:
        # TODO: 'in' comparator
        return_types = set()
        left = node.left
        for comparator, right in node.ops:
            if comparator == 'is':
                return_types.add(bool)
            else:
                resolved_type = self._handle_call(
                    node,
                    BINOP_TO_METHOD[comparator],
                    left.inf_type.getValue(),
                    right.inf_type.getValue()
                )
                return_types.add(resolved_type.getValue())
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
        # TODO: check input types by doing a typecheck for the slice constructor
        node.inf_type = TypeInfo(slice)

    def visit_subscript(self, node: astroid.Subscript) -> None:
        if node.ctx == astroid.Load:
            node.inf_type = self._handle_call(node, '__getitem__', node.value.inf_type.getValue(),
                                                      node.slice.inf_type.getValue())
        elif node.ctx == astroid.Store:
            node.inf_type = self._handle_call(node, '__setitem__', node.value.inf_type.getValue(),
                                                      node.slice.inf_type.getValue())
        elif node.ctx == astroid.Del:
            node.inf_type = self._handle_call(node, '__delitem__', node.value.inf_type.getValue(),
                                                      node.slice.inf_type.getValue())
    ##############################################################################
    # Loops
    ##############################################################################
    def visit_for(self, node):
        iter_type = self._handle_call(node, '__iter__', node.iter.inf_type.getValue()).getValue()
        contained_type = iter_type.__args__[0]
        if isinstance(node.target, astroid.AssignName):
            target_type = self.lookup_type(node.target, node.target.name)
        else:
            # TODO: check whether the following assumption is valid
            # Assume that node.target is a tuple.
            target_type = Tuple[tuple(self.lookup_type(subtarget, subtarget.name) for subtarget in node.target.elts)]

        self.type_constraints.unify(contained_type, target_type)
        node.inf_type = TypeInfo(NoType)

    ##############################################################################
    # Comprehensions
    ##############################################################################
    def visit_comprehension(self, node: astroid.Comprehension) -> None:
        # TODO: refactor code duplication between this and visit_for.
        iter_type = self._handle_call(node, '__iter__', node.iter.inf_type.getValue()).getValue()
        contained_type = iter_type.__args__[0]
        if isinstance(node.target, astroid.AssignName):
            target_type = self.lookup_type(node.target, node.target.name)
        else:
            # TODO: check whether the following assumption is valid
            # Assume that node.target is a tuple.
            target_type = Tuple[tuple(self.lookup_type(subtarget, subtarget.name) for subtarget in node.target.elts)]

        self.type_constraints.unify(contained_type, target_type)
        node.inf_type = TypeInfo(NoType)

    def visit_dictcomp(self, node: astroid.DictComp) -> None:
        key_type = self.type_constraints.resolve(node.key.inf_type.getValue()).getValue()
        val_type = self.type_constraints.resolve(node.value.inf_type.getValue()).getValue()
        node.inf_type = TypeInfo(Dict[key_type, val_type])

    def visit_generatorexp(self, node: astroid.GeneratorExp) -> None:
        elt_type = self.type_constraints.resolve(node.elt.inf_type.getValue()).getValue()
        node.inf_type = TypeInfo(Generator[elt_type, None, None])

    def visit_listcomp(self, node: astroid.ListComp) -> None:
        val_type = self.type_constraints.resolve(node.elt.inf_type.getValue()).getValue()
        node.inf_type = TypeInfo(List[val_type])

    def visit_setcomp(self, node: astroid.SetComp) -> None:
        elt_type = self.type_constraints.resolve(node.elt.inf_type.getValue()).getValue()
        node.inf_type = TypeInfo(Set[elt_type])

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
            # TODO: distinguish between instance, class, and static methods.
            # If node is an instance method, set the first parameter's type to be the class type.
            self.type_constraints.unify(inferred_args[0], _ForwardRef(node.parent.name))

        if any(node.nodes_of_class(astroid.Return)):
            inferred_return = self.type_constraints.resolve(node.type_environment.lookup_in_env('return')).getValue()
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
                t = self.type_constraints.unify(inferred, annotated).getValue()
                combined_args.append(t)

            annotated_rtype = annotated_type.__args__[-1]
            if annotated_rtype is None:
                annotated_rtype = type(None)
            combined_return = self.type_constraints.unify(inferred_return, annotated_rtype).getValue()
        else:
            combined_args, combined_return = inferred_args, inferred_return

        # Update the environment storing the function's type.
        polymorphic_tvars = [arg for arg in combined_args if isinstance(arg, TypeVar)]
        func_type = create_Callable(combined_args, combined_return, polymorphic_tvars)
        self.type_constraints.unify(self.lookup_type(node.parent, node.name), func_type)

    def visit_arguments(self, node: astroid.Arguments) -> None:
        node.inf_type = TypeInfo(NoType)
        for i in range(len(node.annotations)):
            if node.annotations[i] is not None:
                arg_tvar = self.lookup_type(node, node.args[i].name)
                self.type_constraints.unify(arg_tvar, _node_to_type(node.annotations[i]))

    def visit_return(self, node: astroid.Return) -> None:
        t = node.value.inf_type.getValue()
        self.type_constraints.unify(self.lookup_type(node, 'return'), t)
        node.inf_type = TypeInfo(NoType)

    def visit_classdef(self, node: astroid.ClassDef) -> None:
        node.inf_type = TypeInfo(NoType)
        self.type_constraints.unify(self.lookup_type(node.parent, node.name), _ForwardRef(node.name))

        # Update type_store for this class.
        # TODO: include node.instance_attrs as well?
        for attr in node.locals:
            attr_type = self.type_constraints.resolve(node.type_environment.lookup_in_env(attr)).getValue()
            self.type_store.classes[node.name][attr].append(attr_type)
            if isinstance(attr_type, CallableMeta):
                self.type_store.methods[attr].append(attr_type)

    ##############################################################################
    # Statements
    ##############################################################################
    def visit_attribute(self, node: astroid.Attribute) -> None:
        expr_type = node.expr.inf_type.getValue()
        if isinstance(expr_type, _ForwardRef):
            type_name =  expr_type.__forward_arg__
        else:
            type_name = expr_type.__name__
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
        variable_type = self.type_constraints.resolve(
            self._closest_frame(node, node.target.name).type_environment.lookup_in_env(node.target.name)).getValue()
        self.type_constraints.unify(variable_type, _node_to_type(node.annotation.name))
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
