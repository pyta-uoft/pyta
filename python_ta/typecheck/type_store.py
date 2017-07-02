import astroid
from collections import defaultdict
from python_ta.typecheck.base import parse_annotations, class_callable
import os
from typing import Any

TYPE_SHED_PATH = os.path.join(os.path.dirname(__file__), 'typeshed', 'builtins.pyi')


class TypeStore:
    def __init__(self, type_constraints):
        self.type_constraints = type_constraints
        with open(TYPE_SHED_PATH) as f:
            contents = '\n'.join(f.readlines())
        module = astroid.parse(contents)
        self.classes = defaultdict(lambda: defaultdict(list))
        self.functions = defaultdict(list)
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
        for function_def in module.nodes_of_class(astroid.FunctionDef):
            in_class = isinstance(function_def.parent, astroid.ClassDef)
            if in_class:
                tvars = self.classes[function_def.parent.name]['__pyta_tvars']
            else:
                tvars = []
            f_type = parse_annotations(function_def, tvars)
            self.functions[function_def.name].append(f_type)
            if in_class:
                self.classes[function_def.parent.name][function_def.name].append(f_type)

        # Add in constructors
        for klass_name, methods in self.classes.items():
            if '__init__' in methods:
                self.functions[klass_name] = [class_callable(init) for init in methods['__init__']]

    def lookup_function(self, operator, *args):
        """Helper method to lookup a function type given the operator and types of arguments."""
        if args:
            unified = False
            func_types_list = self.functions[operator]
            for func_type in func_types_list:
                # check if args can be unified instead of checking if they are the same!
                unified = True
                for t1, t2 in zip(func_type.__args__[:-1], args):
                    if not self.type_constraints.can_unify(t1, t2):
                        unified = False
                        break
                if unified:
                    return func_type
            if not unified:
                raise KeyError
