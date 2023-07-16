from python_ta.contracts import check_contracts


def test_class_attr_value_restores_to_original_if_violates_rep_inv() -> None:
    """Test to check whether the class attribute value is restored to the original value if a representation invariant
    is violated."""

    @check_contracts
    class Person:
        """
        Representation Invariants:
        - self.age >= 0
        """

        age: int = 0

    my_person = Person()

    try:
        my_person.age = -1
    except AssertionError:
        assert my_person.age == 0


def test_class_attr_value_does_not_exist_if_violates_rep_inv() -> None:
    """Test to check whether the class attribute value does not exist if a representation invariant
    is violated."""

    @check_contracts
    class Person:
        """
        Representation Invariants:
        - self.age >= 0
        """

        age: int

    my_person = Person()

    try:
        my_person.age = -1
    except AssertionError:
        assert not hasattr(my_person, "age")
