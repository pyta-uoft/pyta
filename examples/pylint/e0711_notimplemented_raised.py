class Account:
    """Abstract base class describing the API for an account."""
    _balance: float

    def __init__(self, balance: float) -> None:
        self._balance = balance

    def withdraw(self, amount: float) -> float:
        """Withdraw some money from this account."""
        # Error on the following line: Use `NotImplementedError` instead
        raise NotImplemented
