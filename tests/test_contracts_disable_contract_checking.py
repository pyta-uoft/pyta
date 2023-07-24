import pytest

import python_ta.contracts
from python_ta.contracts import check_contracts


@pytest.fixture
def reset_constant(request):
    original_constant_value = python_ta.contracts.ENABLE_CONTRACT_CHECKING
    constant_value_to_set = getattr(request, "param", original_constant_value)
    python_ta.contracts.ENABLE_CONTRACT_CHECKING = constant_value_to_set
    yield
    python_ta.contracts.ENABLE_CONTRACT_CHECKING = original_constant_value


def test_invalid_attr_type_disable_contract_checking(reset_constant) -> None:
    """
    Test that a Person object is created with an attribute value that doesn't match the specified type annotation but
    with ENABLE_CONTRACT_CHECKING = False so no error is raised.
    """

    @check_contracts
    class Person:
        age: int

    python_ta.contracts.ENABLE_CONTRACT_CHECKING = False
    my_person = Person()
    my_person.age = "John"
    assert my_person.age == "John"
