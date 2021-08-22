from astroid import nodes
from hypothesis import settings
from pytest import skip

from python_ta.typecheck.base import TypeFail

from .. import custom_hypothesis_support as cs

settings.load_profile("pyta")


def test_classdef_attribute_assign():
    """Test whether type of attributes are properly being set."""
    program = (
        f"class Network:\n"
        f"    def __init__(self, name, id):\n"
        f"        self.name = name\n"
        f"        self.id = id"
        f"\n"
        f'rogers = Network("Rogers", 5)\n'
        f'rogers.name = "BoB"\n'
        f'self = Network("asdf", 5)\n'
        f'self.name = "asdfaBoB"\n'
        f"\n"
    )
    module, inferer = cs._parse_text(program)
    classdef_node = next(module.nodes_of_class(nodes.ClassDef))
    for attribute_lst in classdef_node.instance_attrs.values():
        for instance in attribute_lst:
            attribute_type = inferer.type_constraints.resolve(
                classdef_node.type_environment.lookup_in_env(instance.attrname)
            )
            value_type = inferer.type_constraints.resolve(instance.parent.value.inf_type.getValue())
            assert attribute_type == value_type


def test_classdef_method_call():
    """Test whether type of the method call are properly being set"""
    program = (
        f"class Network:\n"
        f"    def __init__(self, name):\n"
        f"        self.name = name\n"
        f"    def get_name(self):\n"
        f"        return self.name\n "
        f"\n"
        f'rogers = Network("Rogers")\n'
        f"rogers.get_name()"
        f"\n"
    )
    module, inferer = cs._parse_text(program, True)
    attribute_node = list(module.nodes_of_class(nodes.Attribute))[1]
    expected_rtype = attribute_node.parent.inf_type.getValue()
    actual_rtype = inferer.type_constraints.resolve(
        attribute_node.inf_type.getValue().__args__[-1]
    ).getValue()
    assert actual_rtype.__name__ == expected_rtype.__name__


def test_classdef_method_call_annotated_concrete():
    """Test whether types of the method calls are properly being set given the annotations."""
    program = (
        f"class Network:\n"
        f"    def __init__(self, name: str) -> None:\n"
        f"        self.name = name\n"
        f"        status = 0\n"
        f"    def set_status(self, status: int) -> int:\n"
        f"        self.status = status\n"
        f"        return self.status\n"
        f"\n"
    )
    module, inferer = cs._parse_text(program)
    for functiondef_node in module.nodes_of_class(nodes.FunctionDef):
        self_name = functiondef_node.args.args[0].name
        actual_type = inferer.type_constraints.resolve(
            functiondef_node.type_environment.lookup_in_env(self_name)
        ).getValue()
        assert actual_type.__forward_arg__ == functiondef_node.parent.name
        for i in range(1, len(functiondef_node.args.annotations)):
            arg_name = functiondef_node.args.args[i].name
            actual_type = inferer.type_constraints.resolve(
                functiondef_node.type_environment.lookup_in_env(arg_name)
            ).getValue()
            assert actual_type.__name__ == functiondef_node.args.annotations[i].name
        expected_rtype = inferer.type_constraints.resolve(
            functiondef_node.parent.type_environment.lookup_in_env(functiondef_node.name)
        ).getValue()
        if functiondef_node.name == "__init__":
            class_type = inferer.type_constraints.resolve(
                functiondef_node.type_environment.lookup_in_env(self_name)
            ).getValue()
            assert class_type == expected_rtype.__args__[-1]
        else:
            assert functiondef_node.returns.name == expected_rtype.__args__[-1].__name__


def test_bad_attribute_access():
    """User tries to access a non-existing attribute; or misspells the attribute name."""
    program = f"x = 1\n" f"x.wrong_name\n"
    module, inferer = cs._parse_text(program)
    expr_node = next(module.nodes_of_class(nodes.Expr))
    expected_msg = "TypeFail: Invalid attribute lookup x.wrong_name"
    assert expr_node.inf_type.getValue() == expected_msg


def test_builtin_method_call_bad_self():
    """User tries to call a method on an object of the wrong type (self)."""
    program = f"x = 1\n" f"x.append(1.0)\n"
    module, inferer = cs._parse_text(program)
    call_node = next(module.nodes_of_class(nodes.Call))
    expected_msg = f"TypeFail: Invalid attribute lookup x.append(1.0)"
    assert isinstance(call_node.inf_type, TypeFail)
    assert call_node.inf_type.getValue() == expected_msg


def test_builtin_method_call_bad_argument():
    """User tries to call a method on an argument of the wrong type."""
    program = f"x = [1, 2, 3]\n" f"x.extend(1)\n"
    module, inferer = cs._parse_text(program)
    call_node = next(module.nodes_of_class(nodes.Call))
    assert isinstance(call_node.inf_type, TypeFail)
