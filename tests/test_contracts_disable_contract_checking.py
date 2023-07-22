import python_ta.contracts
from python_ta.contracts import check_contracts


def test_invalid_attr_type_disable_contract_checking() -> None:
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
    python_ta.contracts.ENABLE_CONTRACT_CHECKING = True
