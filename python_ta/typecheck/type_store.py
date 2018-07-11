import astroid
from astroid.builder import AstroidBuilder
from collections import defaultdict
from python_ta.typecheck.base import parse_annotations, \
    class_callable, accept_failable, _node_to_type
from typing import Callable
import os
from typing import *
from typing import Any
from typing import _ForwardRef

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
            for base in class_def.bases:
                if isinstance(base, astroid.Subscript):
                    tvars = base.slice.as_string().strip('()').replace(" ", "").split(',')
                    self.classes[class_def.name]['__pyta_tvars'] = tvars
            self.classes[class_def.name]['__bases'] = [_node_to_type(base)
                                                       for base in class_def.bases]
            self.classes[class_def.name]['__mro'] = [cls.name for cls in class_def.mro()]
            for node in (nodes[0] for nodes in class_def.locals.values()
                         if isinstance(nodes[0], astroid.AssignName) and
                         isinstance(nodes[0].parent, astroid.AnnAssign)):
                self.classes[class_def.name][node.name] = [
                    parse_annotations(node, tvars)
                ]

    def _parse_functions(self, module: astroid.Module) -> None:
        """Parse the function definitions from typeshed."""
        for function_def in module.nodes_of_class(astroid.FunctionDef):
            in_class = isinstance(function_def.parent, astroid.ClassDef)
            if in_class:
                tvars = self.classes[function_def.parent.name]['__pyta_tvars'][:]
            else:
                tvars = []
            f_type = parse_annotations(function_def, tvars)
            if in_class:
                self.classes[function_def.parent.name][function_def.name].append(f_type)
                self.methods[function_def.name].append(f_type)
            else:
                self.functions[function_def.name].append(f_type)

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
    def lookup_method(self, operator, *args):
        """Helper method to lookup a method type given the operator and types of arguments."""
        if args:
            func_types_list = self.methods[operator]
            # prioritize function types that match the 'self' argument
            func_types_list = sorted(func_types_list,
                                     key=lambda f_tp: f_tp[0].__args__ and
                                                      f_tp[0].__args__[0] == args[0],
                                     reverse=True)
            for func_type, _ in func_types_list:
                if len(args) != len(func_type.__args__) - 1:
                    continue
                if self.type_constraints.can_unify(Callable[list(args), Any],
                                                   Callable[list(func_type.__args__[:-1]), Any]):
                    return func_type
            raise KeyError

    def is_descendant(self, child: type, ancestor: type) -> bool:
        if ancestor == object:
            return True
        child_name = child.__forward_arg__ if isinstance(child, _ForwardRef) \
            else child.__name__
        if child_name in self.classes:
            for base in self.classes[child_name]['__bases']:
                if self.type_constraints.can_unify(base, ancestor) or \
                        self.is_descendant(base, ancestor):
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
