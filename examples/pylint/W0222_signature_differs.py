class StandardBankAccount:
    """A standard bank account."""

    def __init__(self, balance: float) -> None:
        self._balance = balance

    def withdraw(self, amount: float = 20) -> float:
        """Withdraw money from the bank account."""
        if amount <= self._balance:
            self._balance -= amount
            return amount
        else:
            return 0


class PremiumBankAccount(StandardBankAccount):
    """A premium bank account.

    This bank account has more features than the standard bank account,
    but it also costs more.
    """

    def withdraw(self, amount: float) -> float:  # Error on this line
        """Withdraw money from the bank account."""
        if amount <= self._balance - 2:
            # Charge a $2 transaction fee
            self._balance -= 2
            self._balance -= amount
            return amount
        else:
            return 0
