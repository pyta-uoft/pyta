class CashRegister:
    """A cash register for storing money and making change."""
    _current_balance: float

    def __init__(self, balance: float) -> None:
        self._current_balance = balance

    def add_small_coins(self, nickels: int = 0, dimes: int = 0, quarters: int = 0) -> float:
        """Return the dollar value of the small coins."""
        return 0.05 * nickels + 0.10 * dimes + 0.25 * quarters
