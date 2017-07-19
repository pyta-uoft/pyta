import astroid
import nose
from hypothesis import assume, given, settings
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
from typing import Callable
settings.load_profile("pyta")


def test_classdef_attribute_assign():
    """Test whether type of attributes are properly being set."""
    program = f'class Network:\n' \
              f'    def __init__(self, name, id):\n' \
              f'        self.name = name\n' \
              f'        self.id = id' \
              f'\n' \
              f'rogers = Network("Rogers", 5)\n' \
              f'rogers.name = "BoB"\n' \
              f'self = Network("asdf", 5)\n' \
              f'self.name = "asdfaBoB"\n' \
              f'\n'
    module, inferer = cs._parse_text(program)
    classdef_node = next(module.nodes_of_class(astroid.ClassDef))
    for attribute_lst in classdef_node.instance_attrs.values():
        for instance in attribute_lst:
            attribute_type = inferer.type_constraints\
                .lookup_concrete(classdef_node.type_environment.lookup_in_env(instance.attrname))
            value_type = inferer.type_constraints.lookup_concrete(instance.parent.value.type_constraints.type)
            assert attribute_type == value_type


def test_classdef_method_call():
    """Test whether type of the method call are properly being set"""
    program = f'class Network:\n' \
              f'    def __init__(self, name):\n' \
              f'        self.name = name\n' \
              f'    def get_name(self):\n' \
              f'        return self.name\n ' \
              f'\n' \
              f'rogers = Network("Rogers")\n' \
              f'rogers.get_name()' \
              f'\n'
    module, inferer = cs._parse_text(program)
    attribute_node = list(module.nodes_of_class(astroid.Attribute))[1]
    expected_rtype = attribute_node.parent.type_constraints.type
    assert attribute_node.type_constraints.type.__args__[-1] == expected_rtype


def test_classdef_method_call_annotated_concrete():
    """Test whether types of the method calls are properly being set given the annotations."""
    program = f'class Network:\n' \
              f'    def __init__(self: Network, name: str) -> None:\n' \
              f'        self.name = name\n' \
              f'    def get_name(self: Network) -> str:\n' \
              f'        return self.name\n ' \
              f'\n' \
              f'rogers = Network("Rogers")\n' \
              f'rogers.get_name()' \
              f'\n'
    module, inferer = cs._parse_text(program)
    # for self parameter
    for functiondef_node in module.nodes_of_class(astroid.FunctionDef):
        self_name = functiondef_node.args.args[0].name
        actual_type = inferer.type_constraints.lookup_concrete(functiondef_node.type_environment.lookup_in_env(self_name))
        assert actual_type.__forward_arg__ == functiondef_node.args.annotations[0].name
        for i in range(1, len(functiondef_node.args.annotations)):
            arg_name = functiondef_node.args.args[i].name
            actual_type = inferer.type_constraints.lookup_concrete(functiondef_node.type_environment.lookup_in_env(arg_name))
            assert actual_type.__name__ == functiondef_node.args.annotations[i].name
        expected_rtype = inferer.type_constraints\
            .lookup_concrete(functiondef_node.parent.type_environment.lookup_in_env(functiondef_node.name))
        assert functiondef_node.returns.name == expected_rtype.__args__[-1].__name__


if __name__ == '__main__':
    nose.main()
