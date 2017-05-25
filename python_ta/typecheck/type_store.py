import astroid
from collections import defaultdict
from typing import Callable, Any


class TypeStore:
    def __init__(self):
        contents = ''
        with open('typeshed/builtins.pyi') as f:
            contents = '\n'.join(f.readlines())
        module = astroid.parse(contents)
        self.classes = defaultdict(dict)
        self.functions = defaultdict(list)
        for class_def in module.nodes_of_class(astroid.ClassDef):
            # print(class_def.name)
            for function_def in class_def.nodes_of_class(astroid.FunctionDef):
                arg_types = []
                for annotation in function_def.args.annotations:
                    if annotation is None:
                        # assume this is the first parameter 'self'
                        assert arg_types == []
                        arg_types.append(class_def.name)
                    else:
                        arg_types.append(annotation.as_string())
                concrete_arg_types = []
                try:
                    rtype = eval(function_def.returns.as_string())
                except NameError:
                    rtype = function_def.returns.as_string()
                for arg_type in arg_types:
                    try:
                        concrete_arg_type = eval(arg_type)
                    except NameError:
                        concrete_arg_type = arg_type
                    concrete_arg_types.append(concrete_arg_type)
                self.classes[class_def.name][function_def.name] = (Callable[concrete_arg_types, rtype], class_def.name)
                self.functions[function_def.name].append((Callable[concrete_arg_types, rtype], function_def.name))

if __name__ == "__main__":
    a = TypeStore()
    print(a)