import astroid
from collections import defaultdict
from typing import *
from typing import SupportsBytes
import os
TYPE_SHED_PATH = os.path.join(os.path.dirname(__file__), 'typeshed', 'builtins.pyi')


_T = TypeVar('_T')
_T_co = TypeVar('_T_co', covariant=True)
_KT = TypeVar('_KT')
_VT = TypeVar('_VT')
_S = TypeVar('_S')
_T1 = TypeVar('_T1')
_T2 = TypeVar('_T2')
_T3 = TypeVar('_T3')
_T4 = TypeVar('_T4')
_T5 = TypeVar('_T5')
_TT = TypeVar('_TT', bound='type')
class _PathLike: pass


class TypeStore:
    def __init__(self):
        contents = ''
        with open(TYPE_SHED_PATH) as f:
            contents = '\n'.join(f.readlines())
        module = astroid.parse(contents)
        self.classes = defaultdict(dict)
        self.functions = defaultdict(list)
        for class_def in module.nodes_of_class(astroid.ClassDef):
            for base in class_def.bases:
                if isinstance(base, astroid.Subscript):
                    gen = base.value.as_string()
                    tvars = base.slice.as_string().split(',')
                    if gen == 'Generic':
                        self.classes[class_def.name]['__pyta_tvars'] = tvars
            for function_def in class_def.nodes_of_class(astroid.FunctionDef):
                arg_types = []
                for annotation in function_def.args.annotations:
                    if annotation is None:
                        # assume this is the first parameter 'self'
                        assert arg_types == []
                        arg_types.append(eval(
                            self._builtin_to_typing(class_def.name),
                            globals()))
                    else:
                        arg_types.append(eval(
                            self._builtin_to_typing(annotation.as_string()),
                            globals()))

                rtype = eval(self._builtin_to_typing(
                    function_def.returns.as_string()), globals())

                self.classes[class_def.name][function_def.name] = (Callable[arg_types, rtype], class_def.name)
                self.functions[function_def.name].append(Callable[arg_types, rtype])

    def lookup_function(self, operator, *args):
        """Helper method to lookup a function type given the operator and types of arguments."""
        if args:
            found = False
            func_types_list = self.functions[operator]
            for func_type in func_types_list:
                if func_type.__args__[:-1] == args:
                    return func_type
            if not found:
                raise KeyError

    def _builtin_to_typing(self, type_name):
        """Convert a builtin type to its corrsponding typing module class."""
        tvars = self.classes[type_name].get('__pyta_tvars', [])
        tvar_string = f'[{",".join(tvars)}]' if tvars else ''

        if type_name == 'list':
            base_name = 'List'
        elif type_name == 'dict':
            base_name = 'Dict'
        elif type_name == 'tuple':
            base_name = 'Tuple'
        elif type_name == 'set':
            base_name = 'Set'
        elif type_name == 'frozenset':
            base_name = 'FrozenSet'
        elif type_name == 'function':  # special case
            base_name = 'Callable'
            tvar_string = '[[Any], Any]'
        else:
            base_name = type_name
            tvar_string = ''

        return base_name + tvar_string

TYPE_STORE = TypeStore()
