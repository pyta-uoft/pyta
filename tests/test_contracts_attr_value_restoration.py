from python_ta.contracts import check_contracts


def test_class_attr_value_restores_to_original_if_violates_rep_inv() -> None:
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
