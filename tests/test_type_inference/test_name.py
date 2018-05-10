from typing import Callable, Type
import astroid
import nose
from hypothesis import settings, HealthCheck
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


@settings(suppress_health_check=[HealthCheck.too_slow])
def test_builtin_function_name():
    """Test looking up the builtin function `bin`."""
    module, _ = cs._parse_text('bin')
    for node in module.nodes_of_class(astroid.Name):
        assert node.inf_type.getValue() == Callable[[int], str]


@settings(suppress_health_check=[HealthCheck.too_slow])
def test_builtin_class_name():
    """Test looking up the builtin class `int`."""
    module, _ = cs._parse_text('int')
    for node in module.nodes_of_class(astroid.Name):
        assert node.inf_type.getValue() == Type[int]


if __name__ == '__main__':
    nose.main()
