import astroid
from collections import defaultdict
from python_ta.typecheck.base import parse_annotations
import os
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
                    tvars = base.slice.as_string().strip('()').split(',')
                    if gen == 'Generic':
                        self.classes[class_def.name]['__pyta_tvars'] = tvars
            for function_def in class_def.nodes_of_class(astroid.FunctionDef):
                f_type = parse_annotations(function_def, tvars)
                if class_def.name == 'dict':
                    print(f_type, f_type.polymorphic_tvars)
                self.classes[class_def.name][function_def.name].append(f_type)
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
                    if not self.type_constraints.can_unify(t1, t2):
                        unified = False
                        break
                if unified:
                    return func_type
            if not unified:
                raise KeyError


if __name__ == '__main__':
    ts = TypeStore(None)
    print(ts.classes['dict'])
