import astroid
from astroid.builder import AstroidBuilder
from collections import defaultdict
from python_ta.typecheck.base import parse_annotations, \
    _gorg, class_callable, accept_failable, _node_to_type, _collect_tvars, TypeFailFunction
import os
from typing import *
from typing import Any, ForwardRef


TYPE_SHED_PATH = os.path.join(os.path.dirname(__file__), 'typeshed', 'builtins.pyi')


class TypeStore:
    """A representation of the types the entities defined in the current environment."""

    def __init__(self, type_constraints) -> None:
        """Initialize a type store with all the built-in types from the typeshed module."""
        self.type_constraints = type_constraints
        self.classes = defaultdict(lambda: defaultdict(list))
        self.functions = defaultdict(list)
        self.methods = defaultdict(list)

        builder = AstroidBuilder()
        module = builder.file_build(TYPE_SHED_PATH)

        self._parse_classes(module)
        self._parse_functions(module)

        # Add in initializers
        for klass_name, methods in self.classes.items():
            if '__init__' in methods:
                self.functions[klass_name] = [class_callable(init) for init, _ in methods['__init__']]

    def _parse_classes(self, module: astroid.Module) -> None:
        """Parse the class definitions from typeshed."""
        for class_def in module.nodes_of_class(astroid.ClassDef):
            tvars = []
            self.classes[class_def.name]['__bases'] = []
            for base in class_def.bases:
                base_type = _node_to_type(base)
                self.classes[class_def.name]['__pyta_tvars'] = \
                    [tv.__name__ for tv in _collect_tvars(base_type)]
                self.classes[class_def.name]['__bases'].append(base_type)
            self.classes[class_def.name]['__mro'] = [cls.name for cls in class_def.mro()]
            for node in (nodes[0] for nodes in class_def.locals.values()
                         if isinstance(nodes[0], astroid.AssignName) and
                         isinstance(nodes[0].parent, astroid.AnnAssign)):
                self.classes[class_def.name][node.name] = parse_annotations(node, tvars)


    def _parse_functions(self, module: astroid.Module) -> None:
        """Parse the function definitions from typeshed."""
        for function_def in module.nodes_of_class(astroid.FunctionDef):
            in_class = isinstance(function_def.parent, astroid.ClassDef)
            if in_class:
                tvars = self.classes[function_def.parent.name]['__pyta_tvars']
            else:
                tvars = []
            f_type = parse_annotations(function_def, tvars)
            if in_class:
                self.classes[function_def.parent.name][function_def.name].extend(f_type)
                self.methods[function_def.name].extend(f_type)
            else:
                self.functions[function_def.name].extend(f_type)

    def lookup_function(self, operator, *args):
        """Helper method to lookup a function type given the operator and types of arguments."""
        if args:
            func_types_list = self.functions[operator]
            for func_type in func_types_list:
                if len(args) != len(func_type.__args__) - 1:
                    continue
                if self.type_constraints.can_unify(Callable[list(func_type.__args__[:-1]), Any],
                                                   Callable[list(args), Any]):
                    return func_type
            raise KeyError

    @accept_failable
    def lookup_method(self, operator, *args, node):
        """Helper method to lookup a method type given the operator and types of arguments.

        TODO: modify this implementation to use mro.
        """
        if args:
            # First try to do a direct lookup.
            if isinstance(args[0], ForwardRef) and operator in self.classes[args[0].__forward_arg__]:
                for func_type, _ in self.classes[args[0].__forward_arg__][operator]:
                    if len(args) != len(func_type.__args__) - 1:
                        continue
                    if self.type_constraints.can_unify(Callable[list(args), Any],
                                                       Callable[list(func_type.__args__[:-1]), Any]):
                        return func_type

            # If that doesn't work, fall back on a brute force search.
            func_types_list = self.methods[operator]
            for func_type, _ in func_types_list:
                if len(args) != len(func_type.__args__) - 1:
                    continue
                if self.type_constraints.can_unify(Callable[list(args), Any],
                                                   Callable[list(func_type.__args__[:-1]), Any]):
                    return func_type
            return TypeFailFunction(tuple(func_types_list), None, node)

    def is_descendant(self, child: type, ancestor: type) -> bool:
        if (getattr(child, '__origin__', None) is Union or
                getattr(ancestor, '__origin__', None) is Union):
            return self.type_constraints.can_unify(child, ancestor)
        if ancestor == object or ancestor == Any or child == Any:
            return True

        if isinstance(child, ForwardRef):
            child_name = child.__forward_arg__
        elif hasattr(child, '__origin__'):
            child_name = child.__origin__.__name__
        else:
            child_name = child.__name__

        if hasattr(child, '__mro__') and ancestor in child.__mro__:
            return True
        elif hasattr(ancestor, '__mro__') and Protocol in ancestor.__mro__ and issubclass(child, ancestor):
            return True
        elif hasattr(child, '__orig_bases__'):
            for base in child.__orig_bases__:
                if isinstance(base, _GenericAlias) and isinstance(ancestor, _GenericAlias) and \
                   issubclass(_gorg(base), _gorg(ancestor)) and \
                   all([self.type_constraints.can_unify(a1, a2) for a1, a2 in
                         zip(base.__args__, ancestor.__args__)]):
                    return True
        elif child_name in self.classes:
            for base in self.classes[child_name]['__bases']:
                if self.type_constraints.can_unify(base, ancestor) or \
                        self.is_descendant(base, ancestor):
                    # TODO: make sure it is safe to alter type_constraints here
                    self.type_constraints.unify(base, ancestor)
                    return True
        return False


if __name__ == '__main__':
    # Display the TypeStore parsed from typeshed.
    ts = TypeStore(None)
    import pprint
    pprint.pprint(ts.classes)
    pprint.pprint(ts.methods['__iter__'])
    pprint.pprint(ts.functions)
