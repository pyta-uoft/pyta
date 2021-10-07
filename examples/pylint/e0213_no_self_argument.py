class SecretKeeper:
    """A class which stores a secret as a private attribute."""
    _secret: str

    def __init__(self, secret: str) -> None:
        self._secret = secret

    def guess_secret(obj, secret) -> bool:  # Error: 'obj' should be 'self'
        """Guess the private secret."""
        return obj._secret == secret
