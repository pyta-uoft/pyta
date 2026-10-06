import logging

import pytest

from python_ta import contracts

contracts.DEBUG_CONTRACTS = True
from python_ta.contracts import check_contracts


def test_contracts_debug(caplog) -> None:
    """Test to see if _debug function is logging messages correctly"""
    caplog.set_level(logging.DEBUG)

    @check_contracts
    def divide(x: int, y: int) -> int:
        """Return x // y.

        Preconditions:
            - invalid precondition
        """
        return x // y

    divide(6, 2)

    for record in caplog.records:
        assert record.levelname == "DEBUG"
    assert (
        "Warning: precondition invalid precondition could not be parsed as a valid Python expression"
        in caplog.text
    )


@pytest.mark.parametrize(
    "contract",
    [
        "x !== 0",
        "\ud800",
    ],
)
def test_contracts_debug_real_precondition_errors(caplog, contract) -> None:
    """Test syntax and value errors for preconditions."""
    caplog.set_level(logging.DEBUG)

    @check_contracts
    def value_of(x: int) -> int:
        """Return x."""
        return x

    value_of.__doc__ = f"""Return x.

    Preconditions:
        - {contract}
    """
    value_of(1)

    assert (
        f"Warning: precondition {contract} could not be parsed as a valid Python expression"
        in caplog.text
    )


@pytest.mark.parametrize(
    "contract",
    [
        "x !== 0",
        "\ud800",
    ],
)
def test_contracts_debug_real_postcondition_errors(caplog, contract) -> None:
    """Test syntax and value errors for postconditions."""
    caplog.set_level(logging.DEBUG)

    @check_contracts
    def value_of(x: int) -> int:
        """Return x."""
        return x

    value_of.__doc__ = f"""Return x.

    Postconditions:
        - {contract}
    """
    value_of(1)

    assert (
        f"Warning: postcondition {contract} could not be parsed as a valid Python expression"
        in caplog.text
    )


@pytest.mark.parametrize(
    "contract",
    [
        "self.x !== 0",
        "\ud800",
    ],
)
def test_contracts_debug_real_assertion_errors(caplog, contract) -> None:
    """Test syntax and value errors for representation invariants."""
    caplog.set_level(logging.DEBUG)

    class Num:
        """A number."""

        def __init__(self, x: int) -> None:
            self.x = x

    Num.__doc__ = f"""A number.

    Representation Invariants:
        - {contract}
    """
    check_contracts(Num)
    Num(1)

    assert (
        f"Warning: representation invariant {contract} could not be parsed as a valid Python expression"
        in caplog.text
    )


@pytest.mark.parametrize(
    "error",
    [
        MemoryError("out of memory"),
        RecursionError("recursion limit exceeded"),
        OverflowError("compiler limit exceeded"),
    ],
)
def test_contracts_debug_patched_precondition_errors(caplog, monkeypatch, error) -> None:
    """Test patched resource-related errors for preconditions."""
    caplog.set_level(logging.DEBUG)

    def raise_compile_error(*args, **kwargs):
        raise error

    monkeypatch.setattr(contracts, "compile", raise_compile_error, raising=False)

    @check_contracts
    def divide(x: int) -> int:
        """Return x.

        Preconditions:
            - x > 0
        """
        return x

    divide(1)

    assert (
        "Warning: precondition x > 0 could not be parsed as a valid Python expression"
        in caplog.text
    )


@pytest.mark.parametrize(
    "error",
    [
        MemoryError("out of memory"),
        RecursionError("recursion limit exceeded"),
        OverflowError("compiler limit exceeded"),
    ],
)
def test_contracts_debug_patched_postcondition_errors(caplog, monkeypatch, error) -> None:
    """Test patched resource-related errors for postconditions."""
    caplog.set_level(logging.DEBUG)

    def raise_compile_error(*args, **kwargs):
        raise error

    monkeypatch.setattr(contracts, "compile", raise_compile_error, raising=False)

    @check_contracts
    def divide(x: int) -> int:
        """Return x.

        Postconditions:
            - $return_value > 0
        """
        return x

    divide(1)

    assert (
        "Warning: postcondition $return_value > 0 could not be parsed as a valid Python expression"
        in caplog.text
    )


@pytest.mark.parametrize(
    "error",
    [
        MemoryError("out of memory"),
        RecursionError("recursion limit exceeded"),
        OverflowError("compiler limit exceeded"),
    ],
)
def test_contracts_debug_patched_assertion_errors(caplog, monkeypatch, error) -> None:
    """Test patched resource-related errors for representation invariants."""
    caplog.set_level(logging.DEBUG)

    def raise_compile_error(*args, **kwargs):
        raise error

    monkeypatch.setattr(contracts, "compile", raise_compile_error, raising=False)

    class Num:
        """A number.

        Representation Invariants:
            - self.x > 0
        """

        def __init__(self, x: int) -> None:
            self.x = x

    check_contracts(Num)
    Num(1)

    assert (
        "Warning: representation invariant self.x > 0 could not be parsed as a valid Python expression"
        in caplog.text
    )


def test_contracts_debug_instance_attribute(caplog) -> None:
    """Test that setting an instance attribute logs a message naming that attribute"""
    caplog.set_level(logging.DEBUG)

    @check_contracts
    class Person:
        """A class representing a person."""

        name: str
        age: int

        def __init__(self, name: str, age: int) -> None:
            self.name = name
            self.age = age

    person = Person("Allyssa", 21)
    caplog.clear()
    person.name = "Changed"

    assert (
        f"Checking type of attribute name for {Person.__qualname__} instance" in caplog.text
        and f"Checking type of attribute age for {Person.__qualname__} instance" not in caplog.text
    )

    assert "Checking type of attribute __representation_invariants__" not in caplog.text


def test_contracts_debug_unassigned_attribute(caplog) -> None:
    """Test that an annotated but unassigned attribute is reported as a contract violation,
    and that the debug message for that attribute is logged before the error is raised."""
    caplog.set_level(logging.DEBUG)

    @check_contracts
    class Config:
        """A class with an annotated attribute that is never assigned."""

        cache: dict  # declared first, never assigned
        name: str

        def __init__(self, name: str) -> None:
            self.name = name

    with pytest.raises(AssertionError) as excinfo:
        Config("a")
    msg = str(excinfo.value)

    assert f"Checking type of attribute cache for {Config.__qualname__} instance" in caplog.text
    assert f"Attribute cache is not defined for this {Config.__qualname__} instance" in msg
