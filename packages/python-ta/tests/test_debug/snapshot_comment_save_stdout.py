"""
This Python module is designed for testing the run_with_snapshots function's ability to, when a
snapshot comment follows a statement on the same line or is on its own line, return the snapshot
svg to stdout.

This module is intended exclusively for testing purposes and should not be used for any other purpose.
"""


def func(n: int) -> None:
    """
    Function for snapshot comment testing.
    """
    nums = [n, n + 1]  # pyta: snapshot(True, ["--roughjs-config", "seed=12345"], "0.3.1")
    total = sum(nums)
    # pyta: snapshot(True, ["--roughjs-config", "seed=12345"], "0.3.1")


if __name__ == "__main__":
    message = "Hello, world"
    func(1)
