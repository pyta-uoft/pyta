# In reference to issue #799
blah = int


def divide(x: blah, y: blah) -> int:
    """Return x // y."""
    return x // y


# Actual test run in test_contracts.py
def run():
    from python_ta.contracts import check_all_contracts

    check_all_contracts(__name__)

    divide(10, "x")
