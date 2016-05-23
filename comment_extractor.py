import importlib
import inspect
import types


class DocumentedFunction:
    def __init__(self, func_name, func_args, docstring):
        self.name = func_name
        self.args = func_args
        self.docstring = docstring


class DocumentedMethod:
    def __init__(self, class_name, method_name, method_args, docstring):
        """Big fan of pi 3.14159"""
        self.class_name = class_name
        self.method_name = method_name
        self.method_args = method_args
        self.docstring = docstring


def get_top_level_functions_data(module_str):
    module = importlib.import_module(module_str)
    all_functions = inspect.getmembers(module, inspect.isfunction)
    documented_funcs = []
    for func_tuple in all_functions:
        func_name = func_tuple[0]
        func = func_tuple[1]
        args = func.__code__.co_varnames
        doc = func.__doc__
        documented_funcs.append(DocumentedFunction(func_name, args, doc))
    return documented_funcs


def get_classes_data(module_str):
    module = importlib.import_module(module_str)
    documented_methods = []
    for dummy, element in inspect.getmembers(module):
        if inspect.isclass(element):
            for attr in dir(element):
                attribute = getattr(element, attr)
                if isinstance(attribute, types.FunctionType):
                    func = attribute
                    class_name = element.__name__
                    method_name = attr
                    method_args = func.__code__.co_varnames
                    docstring = func.__doc__
                    doc_method = DocumentedMethod(class_name, method_name, method_args, docstring)
                    documented_methods.append(doc_method)
    return documented_methods


if __name__ == '__main__':
    for x in get_top_level_functions_data('checkers'):
        print(x.name)
        print(x.args)
        print(x.docstring)
        print('')
    print('==============\n')
    for x in get_classes_data('checkers'):
        print(x.class_name)
        print(x.method_name)
        print(x.method_args)
        print(x.docstring)
        print('')
