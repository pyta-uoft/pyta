from python_ta import contracts

contracts.DEBUG_CONTRACTS = True
from python_ta.contracts import check_contracts


def test_contracts_debug(caplog) -> None:
    """Test to see if _debug function is logging messages correctly"""

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
