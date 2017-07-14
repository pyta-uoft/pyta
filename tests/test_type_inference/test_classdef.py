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


if __name__ == '__main__':
    nose.main()
