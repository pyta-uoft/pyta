import os.path

from python_ta.debug import SnapshotManager


def test_one_line() -> None:
    with SnapshotManager() as manager:
        num = 123

    assert os.path.exists("snapshot-1.svg")
    # TODO: test the content of the memory diagram against a snapshot


def test_two_lines() -> None:
    line_count = 2
    with SnapshotManager() as manager:
        num = 123
        some_string = "Hello, world"

    assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))


def test_three_lines() -> None:
    line_count = 2
    with SnapshotManager() as manager:
        num = 123
        some_string = "Hello, world"
        num2 = 321

    assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))
