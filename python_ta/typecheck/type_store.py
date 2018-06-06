import astroid
from astroid.builder import AstroidBuilder
from collections import defaultdict
from python_ta.typecheck.base import parse_annotations, class_callable
import os
from typing import Any

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
                self.functions[klass_name] = [class_callable(init) for init in methods['__init__']]

    def _parse_classes(self, module: astroid.Module) -> None:
        """Parse the class definitions from typeshed."""
        for class_def in module.nodes_of_class(astroid.ClassDef):
            tvars = []
            for base in class_def.bases:
                if isinstance(base, astroid.Subscript):
                    gen = base.value.as_string()
                    tvars = base.slice.as_string().strip('()').replace(" ", "").split(',')
                    if gen == 'Generic':
                        self.classes[class_def.name]['__pyta_tvars'] = tvars
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
                tvars = self.classes[function_def.parent.name]['__pyta_tvars']
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
            unified = False
            func_types_list = self.functions[operator]
            for func_type in func_types_list:
                # check if args can be unified instead of checking if they are the same!
                unified = True
                for t1, t2 in zip(func_type.__args__[:-1], args):
                    if not isinstance(self.type_constraints.unify(t1, t2), type):
                        unified = False
                        break
                if unified:
                    return func_type
            if not unified:
                raise KeyError

    def lookup_method(self, operator, *args):
        """Helper method to lookup a method type given the operator and types of arguments."""
        if args:
            unified = False
            func_types_list = self.methods[operator]
            self_type = args[0]
            for func_type in func_types_list:
                if len(args) != len(func_type.__args__) - 1:
                    continue
                unified = True
                for t1, t2 in zip(func_type.__args__[:-1], args):
                    # TODO: replace call to can_unify
                    if not self.type_constraints.can_unify(t1, t2):
                        unified = False
                        break
                if unified:
                    return func_type
            if not unified:
                raise KeyError


if __name__ == '__main__':
    # Display the TypeStore parsed from typeshed.
    ts = TypeStore(None)
    import pprint
    pprint.pprint(ts.classes)
    pprint.pprint(ts.methods['__iter__'])
    pprint.pprint(ts.functions)
