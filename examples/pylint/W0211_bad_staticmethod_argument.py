class CashRegister:
    """A cash register for storing money and making change."""

    def __init__(self, balance: float) -> None:
        self._current_balance = balance

    @staticmethod
    # Error on the following line: Static method with 'self' as first argument
    def add_small_coins(self, nickels: int = 0, dimes: int = 0, quarters: int = 0):
        """Return the dollar value of the small coins."""
        return 0.05 * nickels + 0.10 * dimes + 0.25 * quarters
