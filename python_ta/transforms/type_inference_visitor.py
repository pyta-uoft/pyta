import typing
from itertools import chain
from typing import *
from typing import Callable, ForwardRef, Union, _GenericAlias

import astroid
import astroid.inference
from astroid import nodes
from astroid.transforms import TransformVisitor

from ..typecheck.base import (
    Environment,
    NoType,
    TypeConstraints,
    TypeFail,
    TypeFailAnnotationInvalid,
    TypeFailFunction,
    TypeFailLookup,
    TypeFailReturn,
    TypeFailStarred,
    TypeInfo,
    TypeResult,
    _ann_node_to_type,
    _gorg,
    _node_to_type,
    accept_failable,
    create_Callable_TypeResult,
    failable_collect,
    is_callable,
    wrap_container,
)
from ..typecheck.errors import (
    BINOP_TO_METHOD,
    BINOP_TO_REV_METHOD,
    INPLACE_TO_BINOP,
    UNARY_TO_METHOD,
    binop_error_message,
    subscript_error_message,
    unaryop_error_message,
)
from ..typecheck.type_store import TypeStore


class TypeInferer:
    """The class responsible for inferring types given an astroid AST."""

    type_constraints = TypeConstraints()
    type_store = TypeStore(type_constraints)
    type_constraints.type_store = type_store

    def __init__(self) -> None:
        self.type_constraints.reset()

    def reset(self) -> None:
        self.type_constraints.reset()
        self.type_store = TypeStore(self.type_constraints)
        self.type_constraints.type_store = self.type_store

    ###########################################################################
    # Setting up the environment
    ###########################################################################
    def environment_transformer(self) -> TransformVisitor:
        """Return a TransformVisitor that sets an environment for every node."""
        visitor = TransformVisitor()
        visitor.register_transform(nodes.FunctionDef, self._set_function_def_environment)
        visitor.register_transform(nodes.AsyncFunctionDef, self._set_function_def_environment)
        visitor.register_transform(nodes.ClassDef, self._set_classdef_environment)
        visitor.register_transform(nodes.Module, self._set_module_environment)
        visitor.register_transform(nodes.ListComp, self._set_comprehension_environment)
        visitor.register_transform(nodes.DictComp, self._set_comprehension_environment)
        visitor.register_transform(nodes.SetComp, self._set_comprehension_environment)
        visitor.register_transform(nodes.GeneratorExp, self._set_comprehension_environment)
        visitor.register_transform(nodes.Lambda, self._set_comprehension_environment)
        return visitor

    def _set_module_environment(self, node: nodes.Module) -> None:
        """Method to set environment of a Module node."""
        node.type_environment = Environment()
        for name in node.globals:
            if not any(
                isinstance(elt, (nodes.ImportFrom, nodes.Import)) for elt in node.globals[name]
            ):
                new_tvar = self.type_constraints.fresh_tvar(node.globals[name][0])
                if any(isinstance(elt, nodes.ClassDef) for elt in node.globals[name]):
                    self.type_constraints.unify(new_tvar, Type[ForwardRef(name)], node)
                node.type_environment.globals[name] = new_tvar
        self._populate_local_env(node)

    def _set_classdef_environment(self, node: nodes.ClassDef) -> None:
        """Method to set environment of a ClassDef node."""
        node.type_environment = Environment()
        for name in node.instance_attrs:
            node.type_environment.locals[name] = self.type_constraints.fresh_tvar(
                node.instance_attrs[name][0]
            )
            self.type_store.classes[node.name][name] = [
                (node.type_environment.locals[name], "attribute")
            ]
        for name in node.locals:
            if name in ["__module__", "__qualname__"]:
                node.type_environment.locals[name] = str
            else:
                node.type_environment.locals[name] = self.type_constraints.fresh_tvar(
                    node.locals[name][0]
                )

        self.type_store.classes[node.name]["__bases"] = [_node_to_type(base) for base in node.bases]
        try:
            self.type_store.classes[node.name]["__mro"] = [cls.name for cls in node.mro()]
        except astroid.exceptions.DuplicateBasesError:
            self.type_store.classes[node.name]["__mro"] = [node.name]

    def _set_function_def_environment(self, node: nodes.FunctionDef) -> None:
        """Method to set environment of a FunctionDef node."""
        node.type_environment = Environment()
        # self is a special case
        if (
            node.args.args
            and node.args.args[0].name == "self"
            and isinstance(node.parent, nodes.ClassDef)
        ):
            node.type_environment.locals["self"] = ForwardRef(node.parent.name)
        self._populate_local_env(node)
        self._populate_local_env_attrs(node)
        node.type_environment.locals["return"] = self.type_constraints.fresh_tvar(node)

    def _set_comprehension_environment(self, node: nodes.Comprehension) -> None:
        """Set the environment of a comprehension expression.

        Covers ListComp, SetComp, DictComp, and GeneratorExp."""
        node.type_environment = Environment()
        for name in node.locals:
            node.type_environment.locals[name] = self.type_constraints.fresh_tvar(node)

    def _populate_local_env(self, node: nodes.NodeNG) -> None:
        """Helper to populate locals attributes in type environment of given node."""
        for var_name in node.locals:
            try:
                var_value = node.type_environment.lookup_in_env(var_name)
            except KeyError:
                if any(
                    isinstance(elt, (nodes.ImportFrom, nodes.Import))
                    for elt in node.locals[var_name]
                ):
                    var_value = Any
                else:
                    var_value = self.type_constraints.fresh_tvar(node.locals[var_name][0])
            node.type_environment.locals[var_name] = var_value

    def _populate_local_env_attrs(self, node: nodes.NodeNG) -> None:
        """Store in TypeStore the attributes of any unresolved class names"""
        for attr_node in chain(
            node.nodes_of_class(nodes.Attribute), node.nodes_of_class(nodes.AssignAttr)
        ):
            if (
                isinstance(attr_node.expr, nodes.Name)
                and attr_node.expr.name in node.type_environment.locals
            ):
                class_type = node.type_environment.lookup_in_env(attr_node.expr.name)
                if isinstance(class_type, TypeVar):
                    self.type_store.classes[class_type.__name__]["__mro"] = [class_type.__name__]
                    if not attr_node.attrname in self.type_store.classes[class_type.__name__]:
                        self.type_store.classes[class_type.__name__][attr_node.attrname] = [
                            (self.type_constraints.fresh_tvar(attr_node), "attribute")
                        ]

    ###########################################################################
    # Type inference methods
    ###########################################################################
    def type_inference_transformer(self) -> TransformVisitor:
        """Instantiate a visitor to perform type inference on an AST."""
        type_visitor = TransformVisitor()
        for klass in nodes.ALL_NODE_CLASSES:
            if hasattr(self, f"visit_{klass.__name__.lower()}"):
                type_visitor.register_transform(
                    klass, getattr(self, f"visit_{klass.__name__.lower()}")
                )
            else:
                type_visitor.register_transform(klass, self.visit_default)
        return type_visitor

    def visit_default(self, node: nodes.NodeNG) -> None:
        node.inf_type = NoType()

    ##############################################################################
    # Literals
    ##############################################################################
    def visit_const(self, node: nodes.Const) -> None:
        node.inf_type = TypeInfo(type(node.value))

    def visit_list(self, node: nodes.List) -> None:
        if node.ctx == nodes.Store:
            # List is the target of an assignment; do not give it a type.
            node.inf_type = NoType()
        elif not node.elts:
            node.inf_type = TypeInfo(List[self.type_constraints.fresh_tvar(node)])
        else:
            elt_inf_type = self._unify_elements(node.elts, node)
            node.inf_type = wrap_container(List, elt_inf_type)

    def visit_set(self, node: nodes.Set) -> None:
        if not node.elts:
            node.inf_type = TypeInfo(Set[self.type_constraints.fresh_tvar(node)])
        else:
            elt_inf_type = self._unify_elements(node.elts, node)
            node.inf_type = wrap_container(Set, elt_inf_type)

    def visit_dict(self, node: nodes.Dict) -> None:
        if not node.items:
            node.inf_type = TypeInfo(
                Dict[self.type_constraints.fresh_tvar(node), self.type_constraints.fresh_tvar(node)]
            )
        else:
            key_list, val_list = zip(*node.items)
            key_inf_type = self._unify_elements(key_list, node)
            val_inf_type = self._unify_elements(val_list, node)
            node.inf_type = wrap_container(Dict, key_inf_type, val_inf_type)

    def visit_tuple(self, node: nodes.Tuple) -> None:
        if node.ctx == nodes.Store:
            # Tuple is the target of an assignment; do not give it a type.
            node.inf_type = NoType()
        else:
            node.inf_type = wrap_container(Tuple, *(e.inf_type for e in node.elts))

    def _unify_elements(self, lst: List[nodes.NodeNG], node: nodes.NodeNG) -> TypeResult:
        lst = list(lst)
        elt_inf_type = lst[0].inf_type
        for cur_elt in lst[1:]:
            elt_inf_type = self.type_constraints.unify(elt_inf_type, cur_elt.inf_type, node)
            if isinstance(elt_inf_type, TypeFail):
                return TypeInfo(Any)

        return elt_inf_type

    ##############################################################################
    # Expression types
    ##############################################################################
    def visit_ifexp(self, node: nodes.IfExp) -> None:
        node.inf_type = self.type_constraints.unify(node.body.inf_type, node.orelse.inf_type, node)

    def visit_expr(self, node: nodes.Expr) -> None:
        """Expr nodes take the type of their child."""
        node.inf_type = node.value.inf_type

    ##############################################################################
    # Name lookup and assignment
    ##############################################################################
    def visit_name(self, node: nodes.Name) -> None:
        node.inf_type = self.lookup_inf_type(node, node.name)

    def visit_assign(self, node: nodes.Assign) -> None:
        """Update the enclosing scope's type environment for the assignment's binding(s)."""
        # the type of the expression being assigned
        if isinstance(node.value, nodes.Name):
            expr_inf_type = self.lookup_typevar(node, node.value.name)
        else:
            expr_inf_type = node.value.inf_type

        node.inf_type = NoType()
        for target in node.targets:
            type_result = self._assign_type(target, expr_inf_type, node)
            if isinstance(type_result, TypeFail):
                node.inf_type = type_result
                break

    def visit_annassign(self, node: nodes.AnnAssign) -> None:
        if isinstance(node.target, nodes.AssignAttr):
            var_inf_type = self.lookup_typevar(node.target, node.target.attrname)
        else:
            var_inf_type = self.lookup_typevar(node.target, node.target.name)
        ann_type = _ann_node_to_type(node.annotation)
        self.type_constraints.unify(var_inf_type, ann_type, node)
        if node.value:
            node.targets = [node.target]
            self.visit_assign(node)
        elif isinstance(ann_type, TypeFail):
            node.inf_type = ann_type
        else:
            node.inf_type = NoType()

    def visit_augassign(self, node: nodes.AugAssign) -> None:
        node.inf_type = NoType()

        # lookup method for augmented arithmetic assignment
        method_name = BINOP_TO_METHOD[node.op]
        if isinstance(node.target, nodes.Subscript):
            target_type = node.target.value.inf_type
            binop_result = self._handle_call(
                node.target,
                "__setitem__",
                target_type,
                node.target.slice.inf_type,
                node.value.inf_type,
            )
        else:
            if isinstance(node.target, nodes.AssignName):
                target_type = self.lookup_typevar(node.target, node.target.name)
            elif isinstance(node.target, nodes.AssignAttr):
                target_type = self._lookup_attribute_type(
                    node.target, node.target.expr.inf_type, node.target.attrname
                )
            binop_result = self._handle_call(node, method_name, target_type, node.value.inf_type)
        if isinstance(binop_result, TypeFail):
            # on failure, fallback to method corresponding to standard operator
            boolop = INPLACE_TO_BINOP[node.op]
            method_name = BINOP_TO_METHOD[boolop]
            arithm_type = self._arithm_convert(node, method_name, target_type, node.value.inf_type)
            if arithm_type:
                binop_result = arithm_type
            else:
                binop_result = self._handle_call(
                    node, method_name, target_type, node.value.inf_type
                )

        type_result = self._assign_type(node.target, binop_result, node)
        if isinstance(type_result, TypeFail):
            node.inf_type = type_result

    @accept_failable
    def _assign_type(self, target: nodes.NodeNG, expr_type: type, node: nodes.Assign) -> TypeResult:
        """Update the type environment so that the target is bound to the given type."""
        if isinstance(target, nodes.AssignName):
            # A single identifier, e.g. x = ...
            target_type_var = self.lookup_typevar(target, target.name)
            return self.type_constraints.unify(target_type_var, expr_type, node)
        elif isinstance(target, nodes.AssignAttr):
            # Attribute mutation, e.g. x.y = ...
            attr_type = self._lookup_attribute_type(target, target.expr.inf_type, target.attrname)
            return self.type_constraints.unify(attr_type, expr_type, node)
        elif isinstance(target, nodes.Tuple):
            # Unpacking assignment, e.g. x, y = ...
            if getattr(expr_type, "__origin__", None) is tuple:
                assign_result = self._assign_tuple(target, expr_type, node)
            else:
                assign_result = self._handle_call(target, "__iter__", expr_type)

                target_tvars = self._get_tuple_targets(target)
                starred_target_found = False
                for tvar, elt in zip(target_tvars, target.elts):
                    if isinstance(elt, nodes.Starred) and not starred_target_found:
                        starred_target_found = True
                        unif_result = assign_result >> (
                            lambda t: self.type_constraints.unify(tvar, List[t.__args__[0]], node)
                        )
                    elif isinstance(elt, nodes.Starred) and starred_target_found:
                        unif_result = TypeFailStarred(node)
                    else:
                        unif_result = assign_result >> (
                            lambda t: self.type_constraints.unify(tvar, t.__args__[0], node)
                        )

                    if isinstance(unif_result, TypeFail):
                        return unif_result
            return assign_result
        elif isinstance(target, nodes.Subscript):
            # TODO: previous case must recursively handle this one
            return self._handle_call(
                target, "__setitem__", target.value.inf_type, target.slice.inf_type, expr_type
            )

    def _assign_tuple(self, target: nodes.Tuple, value: Any, node: nodes.Assign) -> TypeResult:
        """Unify tuple of type variables and tuple of types, within context of Assign statement."""
        starred_index = None
        for i in range(len(target.elts)):
            if isinstance(target.elts[i], nodes.Starred):
                if starred_index is None:
                    starred_index = i
                else:
                    return TypeFailStarred(node)

        target_tvars = self._get_tuple_targets(target)

        if starred_index is not None:
            starred_length = len(value.__args__) - len(target.elts) + 1
            starred_subvalues = node.value.elts[starred_index : starred_index + starred_length]
            starred_value = wrap_container(List, self._unify_elements(starred_subvalues, node))

            starred_target_tvar = target_tvars[starred_index]

            unif_result = self.type_constraints.unify(starred_target_tvar, starred_value, node)
            if isinstance(unif_result, TypeFail):
                return unif_result

            nonstarred_values = Tuple[
                value.__args__[:starred_index] + value.__args__[starred_index + starred_length :]
            ]
            nonstarred_targets = target_tvars
            nonstarred_targets.remove(nonstarred_targets[starred_index])

        else:
            nonstarred_values = value
            nonstarred_targets = target_tvars

        nonstarred_target_tuple = wrap_container(Tuple, *nonstarred_targets)

        unif_result = self.type_constraints.unify(nonstarred_target_tuple, nonstarred_values, node)
        if isinstance(unif_result, TypeFail):
            return unif_result

        assign_result = TypeInfo(value)
        return assign_result

    def _get_tuple_targets(self, t: nodes.Tuple) -> List[type]:
        target_tvars = []
        for subtarget in t.elts:
            if isinstance(subtarget, nodes.AssignAttr):
                target_tvars.append(
                    self._lookup_attribute_type(
                        subtarget, subtarget.expr.inf_type, subtarget.attrname
                    )
                )
            elif isinstance(subtarget, nodes.Starred):
                if isinstance(subtarget.value, nodes.AssignAttr):
                    target_tvars.append(
                        self.lookup_typevar(subtarget.value, subtarget.value.attrname)
                    )
                else:
                    target_tvars.append(self.lookup_typevar(subtarget.value, subtarget.value.name))
            elif isinstance(subtarget, nodes.Subscript):
                target_tvars.append(
                    self._handle_call(
                        subtarget, "__getitem__", subtarget.value.inf_type, subtarget.slice.inf_type
                    )
                )
            else:
                target_tvars.append(self.lookup_typevar(subtarget, subtarget.name))
        return target_tvars

    @accept_failable
    def _lookup_attribute_type(
        self, node: nodes.NodeNG, class_type: type, attribute_name: str
    ) -> TypeResult:
        """Given the node, class and attribute name, return the type of the attribute."""
        class_type = self.type_constraints.resolve(class_type)
        class_name, _, _ = self.get_attribute_class(class_type)
        if (
            class_name in self.type_store.classes
            and attribute_name in self.type_store.classes[class_name]
        ):
            return self.type_constraints.resolve(
                self.type_store.classes[class_name][attribute_name][0][0]
            )
        closest_frame = node.scope().lookup(class_name)[0]
        try:
            class_env = closest_frame.locals[class_name][0].type_environment
            result = self.type_constraints.resolve(class_env.lookup_in_env(attribute_name))
        except (KeyError, AttributeError):
            result = TypeFailLookup(self.type_constraints.get_tnode(class_type), node, node.parent)
        return result

    def lookup_typevar(self, node: nodes.NodeNG, name: str) -> TypeResult:
        """Given a variable name, return the equivalent TypeVar in the closest scope relative to given node."""
        cur_node = node

        while cur_node is not None:
            # Get first parent node with scope
            cur_scope = cur_node.scope()
            try:
                # Attempt to look up variable in type environment
                return TypeInfo(cur_scope.type_environment.lookup_in_env(name))
            except KeyError:
                # Variable not found in scope of current node, search parent node
                cur_node = cur_scope.parent

        # If root of astroid tree is reached with no variable found,
        # search builtins and TypeStore for variable type
        if name in self.type_store.classes:
            result = TypeInfo(Type[__builtins__[name]])
        elif name.lower() in self.type_store.classes:
            result = TypeInfo(Type[__builtins__[name.lower()]])
        elif name in self.type_store.functions:
            result = TypeInfo(
                Union[tuple([func_type for func_type, _ in self.type_store.functions[name]])]
            )
        else:
            result = TypeFail("Unbound identifier")

        return result

    def lookup_inf_type(self, node: nodes.NodeNG, name: str) -> TypeResult:
        """Given a variable name, return a TypeResult object containing the type in the closest scope relative to given node."""
        tvar = self.lookup_typevar(node, name)
        return self.type_constraints.resolve(tvar)

    ##############################################################################
    # Operation nodes
    ##############################################################################
    @accept_failable
    def get_call_signature(self, c: type, node: nodes.NodeNG) -> TypeResult:
        """Check for and return initializer function signature when using class name as Callable.
        Return Callable unmodified otherwise.

        :param c: Class, ForwardRef to a class, or Callable
        :param node: nodes.Call node where function call is occurring
        """
        # Any is interpreted as a function that can take any arguments.
        if c is Any:
            return TypeInfo(Callable[..., Any])
        # Callable type; e.g., 'Callable[[int], int]'
        elif is_callable(c):
            return TypeInfo(c)
        # Union of Callables
        elif getattr(c, "__origin__", None) is Union and all(
            is_callable(elt) for elt in c.__args__
        ):
            return TypeInfo(c)
        # Class types; e.g., 'Type[ForwardRef('A')]'
        elif getattr(c, "__origin__", None) is type:
            class_type = c.__args__[0]
            if isinstance(class_type, ForwardRef):
                class_name = c.__args__[0].__forward_arg__
            else:
                class_name = class_type.__name__

            if "__init__" in self.type_store.classes[class_name]:
                matching_init_funcs = []
                for func_type, _ in self.type_store.classes[class_name]["__init__"]:
                    new_func_type = Callable[list(func_type.__args__[1:-1]), func_type.__args__[0]]
                    matching_init_funcs.append(new_func_type)
                init_func = Union[tuple(matching_init_funcs)]
            else:
                # Classes declared without initializer
                init_func = Callable[[], class_type]
            return TypeInfo(init_func)
        # Class instances; e.g., 'ForwardRef('A')'
        elif isinstance(c, ForwardRef):
            class_type = c
            class_name = c.__forward_arg__

            if "__call__" in self.type_store.classes[class_name]:
                call_args = list(self.type_store.classes[class_name]["__call__"][0][0].__args__)
                call_func = Callable[call_args[1:-1], call_args[-1]]
                return TypeInfo(call_func)
            else:
                class_tnode = self.type_constraints.get_tnode(class_type)
                return TypeFailLookup(class_tnode, node, node.parent)
        else:
            return TypeFailFunction((c,), None, node)

    def visit_call(self, node: nodes.Call) -> None:
        f = self.type_constraints.resolve(node.func.inf_type)
        func_inf_type = self.get_call_signature(f, node.func)
        arg_inf_types = [arg.inf_type for arg in node.args]

        node.inf_type = self.type_constraints.unify_call(func_inf_type, *arg_inf_types, node=node)

    def visit_binop(self, node: nodes.BinOp) -> None:
        left_inf, right_inf = node.left.inf_type, node.right.inf_type

        method_name = BINOP_TO_METHOD[node.op]
        # attempt to obtain a common arithmetic type
        arithm_type = self._arithm_convert(node, method_name, left_inf, right_inf)
        if arithm_type:
            node.inf_type = arithm_type
        else:
            rev_method_name = BINOP_TO_REV_METHOD[node.op]
            l_type = self._handle_call(node, method_name, left_inf, right_inf)
            r_type = self._handle_call(node, rev_method_name, right_inf, left_inf)

            if self.type_store.is_descendant(right_inf.getValue(), left_inf.getValue()):
                if isinstance(r_type, TypeFail) and isinstance(l_type, TypeInfo):
                    node.inf_type = l_type
                else:
                    node.inf_type = r_type
            else:
                if isinstance(l_type, TypeFail) and isinstance(r_type, TypeInfo):
                    node.inf_type = r_type
                else:
                    node.inf_type = l_type

    @accept_failable
    def _arithm_convert(
        self, node: nodes.NodeNG, method: str, t1: type, t2: type
    ) -> Optional[TypeInfo]:
        if t1 is complex and t2 is complex:
            common_type = complex
        elif (t1 is complex and issubclass(t2, typing.SupportsFloat)) or (
            t2 is complex and issubclass(t1, typing.SupportsFloat)
        ):
            # TODO: handle complex better. Looks like int, float don't
            # support typing.SupportsComplex.
            common_type = complex
        elif (t1 is float and issubclass(t2, typing.SupportsFloat)) or (
            t2 is float and issubclass(t1, typing.SupportsFloat)
        ):
            common_type = float
        else:
            common_type = None

        if common_type:
            return self._handle_call(node, method, common_type, common_type)
        else:
            return None

    def visit_unaryop(self, node: nodes.UnaryOp) -> None:
        # 'not' is not a function, so this handled as a separate case.
        if node.op == "not":
            node.inf_type = TypeInfo(bool)
        else:
            method_name = UNARY_TO_METHOD[node.op]
            node.inf_type = self._handle_call(node, method_name, node.operand.inf_type)

    def visit_boolop(self, node: nodes.BoolOp) -> None:
        node.inf_type = self._unify_elements(node.values, node)
        if isinstance(node.inf_type, TypeFail):
            node.inf_type = TypeInfo(Any)

    def _handle_compare(
        self, node: nodes.NodeNG, comparator: str, left: nodes.NodeNG, right: nodes.NodeNG
    ) -> TypeResult:
        """Helper function to lookup a comparator, find the equivalent function call,
        and unify call with given arguments.
        """
        if comparator == "is" or comparator == "is not":
            return TypeInfo(bool)
        elif comparator == "in" or comparator == "not in":
            return self._handle_call(
                node, BINOP_TO_METHOD[comparator], right.inf_type, left.inf_type
            )
        else:
            return self._handle_call(
                node, BINOP_TO_METHOD[comparator], left.inf_type, right.inf_type
            )

    def visit_compare(self, node: nodes.Compare) -> None:
        left = node.left
        compare_type = self._handle_compare(node, node.ops[0][0], left, node.ops[0][1])

        for comparator, right in node.ops[1:]:
            resolved_type = self._handle_compare(node, comparator, left, right)
            compare_type = self.type_constraints.unify(compare_type, resolved_type, node)

        node.inf_type = compare_type

    ##############################################################################
    # Subscripting
    ##############################################################################
    def visit_index(self, node: nodes.Index) -> None:
        node.inf_type = node.value.inf_type

    def visit_slice(self, node: nodes.Slice) -> None:
        lower_type = node.lower.inf_type if node.lower else type(None)
        upper_type = node.upper.inf_type if node.upper else type(None)
        step_type = node.step.inf_type if node.step else type(None)
        node.inf_type = self._handle_call(
            node, "__init__", slice, lower_type, upper_type, step_type
        )
        node.inf_type = node.inf_type >> (
            lambda t: TypeInfo(slice) if t == type(None) else TypeInfo(t)
        )

    def visit_extslice(self, node: nodes.ExtSlice):
        unif_res = failable_collect(dim.inf_type for dim in node.dims)
        node.inf_type = unif_res >> (lambda lst: wrap_container(Tuple, *lst))

    def visit_subscript(self, node: nodes.Subscript) -> None:
        if isinstance(node.slice.inf_type, TypeFail):
            node.inf_type = node.slice.inf_type
        elif node.ctx == nodes.Load:
            try:
                val_inf_type = self.type_constraints.resolve(node.value.inf_type)
                value_gorg = val_inf_type >> _gorg
            except AttributeError:
                value_gorg = None

            if value_gorg is type and isinstance(node.slice, nodes.Index):
                if isinstance(node.slice.value, nodes.Tuple):
                    node.inf_type = wrap_container(
                        _node_to_type(node.value), *_node_to_type(node.slice.value)
                    )
                else:
                    node.inf_type = wrap_container(
                        _node_to_type(node.value), _node_to_type(node.slice.value)
                    )
            else:
                node.inf_type = self._handle_call(
                    node, "__getitem__", node.value.inf_type, node.slice.inf_type
                )
        elif node.ctx == nodes.Store:
            node.inf_type = NoType()
        elif node.ctx == nodes.Del:
            node.inf_type = self._handle_call(
                node, "__delitem__", node.value.inf_type, node.slice.inf_type
            )

    ##############################################################################
    # Loops
    ##############################################################################
    def visit_for(self, node: Union[nodes.For, nodes.Comprehension]) -> None:
        iter_type_result = self._handle_call(node, "__iter__", node.iter.inf_type)
        if isinstance(node.target, nodes.AssignName):
            target_inf_type = self.lookup_inf_type(node.target, node.target.name)
        elif isinstance(node.target, nodes.AssignAttr):
            target_inf_type = self._lookup_attribute_type(
                node.target, node.target.expr.inf_type, node.target.attrname
            )
        elif isinstance(node.target, nodes.Subscript):
            target_inf_type = iter_type_result >> (
                lambda t: self._handle_call(
                    node.target,
                    "__setitem__",
                    node.target.value.inf_type,
                    node.target.slice.inf_type,
                    t.__args__[0],
                )
            )
        elif isinstance(node.target, nodes.Tuple):
            target_inf_type = wrap_container(
                Tuple,
                *[
                    self.lookup_inf_type(subtarget, subtarget.name)
                    for subtarget in node.target.elts
                ],
            )
        iter_type_result >> (
            lambda t: self.type_constraints.unify(t.__args__[0], target_inf_type, node)
        )
        node.inf_type = iter_type_result if isinstance(iter_type_result, TypeFail) else NoType()

    ##############################################################################
    # Comprehensions
    ##############################################################################
    def visit_comprehension(self, node: nodes.Comprehension) -> None:
        self.visit_for(node)

    def visit_dictcomp(self, node: nodes.DictComp) -> None:
        key_inf_type = self.type_constraints.resolve(node.key.inf_type)
        val_inf_type = self.type_constraints.resolve(node.value.inf_type)
        node.inf_type = wrap_container(Dict, key_inf_type, val_inf_type)

    def visit_generatorexp(self, node: nodes.GeneratorExp) -> None:
        elt_inf_type = self.type_constraints.resolve(node.elt.inf_type)
        node.inf_type = wrap_container(Generator, elt_inf_type, None, None)

    def visit_listcomp(self, node: nodes.ListComp) -> None:
        val_inf_type = self.type_constraints.resolve(node.elt.inf_type)
        node.inf_type = wrap_container(List, val_inf_type)

    def visit_setcomp(self, node: nodes.SetComp) -> None:
        elt_inf_type = self.type_constraints.resolve(node.elt.inf_type)
        node.inf_type = wrap_container(Set, elt_inf_type)

    @accept_failable
    def _handle_call(self, node: nodes.NodeNG, function_name: str, *arg_types: type) -> TypeResult:
        """Helper to lookup a function and unify it with given arguments.
        Return the return type of unified function call.
        """
        arg_inf_types = [self.type_constraints.resolve(arg) for arg in arg_types]
        func_type = self.type_store.lookup_method(function_name, *arg_inf_types, node=node)

        return self.type_constraints.unify_call(func_type, *arg_types, node=node)

    ##############################################################################
    # Definitions
    ##############################################################################
    def visit_functiondef(self, node: nodes.FunctionDef) -> None:
        node.inf_type = NoType()

        # Get the inferred type of the function arguments
        inferred_args = [self.lookup_inf_type(node, arg) for arg in node.argnames()]

        if isinstance(node.parent, nodes.ClassDef) and inferred_args:
            # first argument is special in these cases
            if node.type == "method":
                self.type_constraints.unify(inferred_args[0], ForwardRef(node.parent.name), node)
            elif node.type == "classmethod":
                self.type_constraints.unify(
                    inferred_args[0], Type[ForwardRef(node.parent.name)], node
                )

        # Get inferred return type
        if any(node.nodes_of_class(nodes.Return)):
            return_node = list(node.nodes_of_class(nodes.Return))[-1]
            if isinstance(return_node.inf_type, TypeFail):
                inferred_return = return_node.inf_type
            else:
                inferred_return = self.lookup_inf_type(node, "return")
        elif node.name == "__init__" and inferred_args:
            inferred_return = inferred_args[0]
        else:
            inferred_return = TypeInfo(type(None))

        # Update the environment storing the function's type.
        polymorphic_tvars = set()
        for arg in inferred_args + [inferred_return]:
            arg >> (lambda a: polymorphic_tvars.add(a.__name__) if isinstance(a, TypeVar) else None)

        # Create function signature
        func_type = create_Callable_TypeResult(
            failable_collect(inferred_args), inferred_return, polymorphic_tvars
        )

        # Check for optional arguments, create a Union of function signatures if necessary
        num_defaults = len(node.args.defaults)
        if num_defaults > 0 and not isinstance(func_type, TypeFail):
            for i in range(num_defaults):
                opt_args = inferred_args[: -1 - i]
                opt_func_type = create_Callable_TypeResult(
                    failable_collect(opt_args), inferred_return, polymorphic_tvars
                )
                func_type = func_type >> (
                    lambda f: opt_func_type >> (lambda opt_f: TypeInfo(Union[f, opt_f]))
                )

        # Final type signature unify
        func_name = self.lookup_inf_type(node.parent, node.name)
        result = self.type_constraints.unify(func_name, func_type, node)
        if isinstance(result, TypeFail):
            node.inf_type = result

    def visit_asyncfunctiondef(self, node: nodes.AsyncFunctionDef) -> None:
        self.visit_functiondef(node)

    def visit_lambda(self, node: nodes.Lambda) -> None:
        inferred_args = [self.lookup_inf_type(node, arg) for arg in node.argnames()]
        inferred_return = node.body.inf_type

        polymorphic_tvars = set()
        for arg in inferred_args + [inferred_return]:
            arg >> (lambda a: polymorphic_tvars.add(a.__name__) if isinstance(a, TypeVar) else None)

        node.inf_type = create_Callable_TypeResult(
            failable_collect(inferred_args), inferred_return, polymorphic_tvars
        )

    def visit_arguments(self, node: nodes.Arguments) -> None:
        node.inf_type = NoType()
        if any(annotation is not None for annotation in node.annotations):
            for i in range(len(node.annotations)):
                arg_tvar = self.lookup_typevar(node, node.args[i].name)

                if node.annotations[i] is not None:
                    ann_type = _ann_node_to_type(node.annotations[i])
                    result = self.type_constraints.unify(arg_tvar, ann_type, node)
                    if isinstance(result, TypeFail):
                        node.inf_type = result
                else:
                    self.type_constraints.unify(arg_tvar, Any, node)

    def visit_return(self, node: nodes.Return) -> None:
        return_tvar = self.lookup_typevar(node, "return")
        # TODO: Replace with isinstance() once proper TypeFail subclass is created for unbound indentifiers
        if return_tvar == TypeFail("Unbound identifier"):
            return_target = TypeFailReturn(node)
        else:
            return_target = return_tvar

        if node.value is not None and getattr(node.scope(), "returns", None) is not None:
            return_annotation = _ann_node_to_type(node.scope().returns)
            return_value = self.type_constraints.unify(node.value.inf_type, return_annotation, node)
        elif node.value is not None:
            return_value = node.value.inf_type
        else:
            return_value = TypeInfo(None)

        val_inf_type = self.type_constraints.unify(return_value, return_target, node)
        node.inf_type = val_inf_type if isinstance(val_inf_type, TypeFail) else NoType()

    def visit_classdef(self, node: nodes.ClassDef) -> None:
        node.inf_type = NoType()

        # Update type_store for this class.
        # TODO: include node.instance_attrs as well?
        for attr in node.locals:
            attr_inf_type = self.type_constraints.resolve(node.type_environment.lookup_in_env(attr))
            attr_inf_type >> (
                lambda a: self.type_store.methods[attr].append((a, node.locals[attr][0].type))
                if is_callable(a)
                else None
            )
            attr_inf_type >> (
                lambda a: self.type_store.classes[node.name][attr].append(
                    (a, node.locals[attr][0].type if is_callable(a) else "attribute")
                )
            )

    @accept_failable
    def get_attribute_class(self, t: type) -> Tuple[str, type, bool]:
        """Check for and return name and type of class represented by type t."""
        is_inst_expr = True

        # TypeVar; e.g., 'TypeVar('_T1')' corresponding to a function argument
        if isinstance(t, TypeVar):
            return t.__name__, t, None

        # Class type: e.g., 'Type[ForwardRef('A')]'
        if getattr(t, "__origin__", None) is type:
            class_type = t.__args__[0]
            is_inst_expr = False
        # Instance of class or builtin type; e.g., 'ForwardRef('A')' or 'int'
        else:
            class_type = t

        if isinstance(class_type, ForwardRef):
            class_name = class_type.__forward_arg__
        elif isinstance(class_type, _GenericAlias):
            class_name = class_type._name
        else:
            class_name = getattr(t, "__name__", None)

        # TODO: the condition below is too general
        if class_name is not None and class_name not in self.type_store.classes:
            class_name = class_name.lower()

        return class_name, class_type, is_inst_expr

    def visit_attribute(self, node: nodes.Attribute) -> None:
        expr_inf_type = self.type_constraints.resolve(node.expr.inf_type)
        result = self.get_attribute_class(expr_inf_type)
        if not isinstance(result, TypeFail):
            class_name, class_type, inst_expr = result

            if class_type == Any:
                node.inf_type = TypeInfo(Any)
            elif class_name in self.type_store.classes:
                attribute_type = None
                for par_class_type in self.type_store.classes[class_name]["__mro"]:
                    attribute_type = self.type_store.classes[par_class_type].get(node.attrname)
                    if attribute_type:
                        break
                if attribute_type is None:
                    class_tnode = self.type_constraints.get_tnode(class_type)
                    node.inf_type = TypeFailLookup(class_tnode, node, node.parent)
                else:
                    func_type, method_type = attribute_type[0]
                    if (
                        is_callable(func_type)
                        and method_type == "method"
                        and inst_expr
                        or method_type == "classmethod"
                    ):
                        # Replace polymorphic type variables with fresh type variables
                        fresh_func_type = self.type_constraints.fresh_callable(func_type, node)
                        self.type_constraints.unify(fresh_func_type.__args__[0], class_type)
                        # Create new Callable to avoid modifying elements of type store
                        new_func_type = create_Callable_TypeResult(
                            fresh_func_type.__args__[1:-1], fresh_func_type.__args__[-1]
                        )
                    else:
                        new_func_type = TypeInfo(func_type)
                    node.inf_type = new_func_type
            else:
                class_tnode = self.type_constraints.get_tnode(class_type)
                node.inf_type = TypeFailLookup(class_tnode, node, node.parent)
        else:
            node.inf_type = result

    def visit_module(self, node: nodes.Module) -> None:
        node.inf_type = NoType()


# Main function (useful for quick debugging)
def main(source: str) -> Tuple[nodes.Module, TypeInferer]:
    """Parse a string representing source text, and perform a typecheck.

    Return the astroid Module node (with the type_constraints attribute set
    on all nodes in the tree) and TypeInferer object.
    """
    module = astroid.parse(source)
    type_inferer = TypeInferer()
    type_inferer.environment_transformer().visit(module)
    type_inferer.type_inference_transformer().visit(module)
    return module, type_inferer
