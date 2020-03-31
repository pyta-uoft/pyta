import pytest
from python_ta.contracts import check_contracts


@check_contracts
class Animal:
    """
    Represents animals

    Representation Invariants:
    - self.num_legs >= 2
    - len(self.diet) > 0
    """

    def __init__(self, num_legs, diet):
        self.num_legs = num_legs
        self.diet = diet


@check_contracts
class Bird(Animal):
    """
    Representation Invariants:
    - self.wing_span > 0
    """

    def __init__(self, num_legs, diet, wing_span):
        super().__init__(num_legs, diet)
        self.wing_span = wing_span


birdie = Bird(2, "Omnivore", 10.3)


def test_change_wingspan_valid() -> None:
    """
    Change the wing_span to a valid value.
    """
    birdie.wing_span = 9.5


def test_change_diet_invalid() -> None:
    """
    Change diet to something invalid. Expect exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        birdie.diet = ""
    msg = str(excinfo.value)
    assert 'len(self.diet)' in msg


def test_change_wingspan_invalid() -> None:
    """
    Change wingspan to something invalid. Expect exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        birdie.diet = "Omnivore"  # Change it back to a valid value
        birdie.wing_span = 0
    msg = str(excinfo.value)
    assert 'self.wing_span > 0' in msg
