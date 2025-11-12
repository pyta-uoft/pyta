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


def test_rep_inv_missing_self_raises_suggestion(capsys) -> None:
    """Test that a representation invariant referring to an attribute missing the `self.`
    prefix will print a suggestion on NameError."""

    @check_contracts
    class Person:
        """
        Representation Invariants:
        - age >= 0
        """

        age: int

    my_person = Person()
    my_person.age = 10

    output = capsys.readouterr()
    assert (
        "Could not find `age` when evaluating representation invariant. Did you mean `self.age`?"
        in output.out
    )


def test_rep_inv_missing_name_no_suggestion(capsys) -> None:
    """Test that a representation invariant with a missing name that is not an instance attribute does
    not result in a suggestion on NameError."""

    @check_contracts
    class Person:
        """
        Representation Invariants:
        - weight >= 0
        """

        age: int

    my_person = Person()
    my_person.age = 10

    output = capsys.readouterr()
    assert "Did you mean `self.weight`?" not in output.out
