import os.path

from python_ta.debug import SnapshotManager


def func_one_line(tmp_path) -> SnapshotManager:
    with SnapshotManager(output_filepath=tmp_path, include=("func_one_line",)) as manager:
        num = 123
    return manager


def func_multi_line() -> SnapshotManager:
    with SnapshotManager(include=("func_multi_line",)) as manager:
        num = 123
        some_string = "Hello, world"
        num2 = 321
        arr = [some_string, "string 123321"]
    return manager


def func_mutation():
    with SnapshotManager(include=("func_mutation",)) as manager:
        num = 123
        num = 321
    return manager


def func_for_loop():
    with SnapshotManager(include=("func_for_loop",)) as manager:
        nums = [1, 2, 3]
        for i in range(len(nums)):
            nums[i] = nums[i] + 1
    return manager


# TODO: we are taking a snapshot even for statements, clarify if this is necessary
def func_if_else() -> None:
    with SnapshotManager():
        num = 10
        if num > 5:
            result = "greater"
        else:
            result = "lesser"


def func_while() -> None:
    line_count = 2
    with SnapshotManager():
        num = 0
        while num < 3:
            num += 1

    assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))


def assert_output_files_match(snapshot_count: int, output_path: str, actual_path: str):
    for i in range(snapshot_count):
        with (
            open(os.path.join(output_path, f"snapshot-{i}.svg")) as actual_file,
            open(os.path.join(actual_path, f"snapshot-{i}.svg")) as expected_file,
        ):
            actual_svg = actual_file.read()
            expected_svg = expected_file.read()
            assert actual_svg == expected_svg


def test_multi_line(tmp_path) -> None:
    manager = func_multi_line()
    snapshot_count = manager.get_snapshot_count()
    # assert_output_files_match(snapshot_count, tmp_path.name, "snapshot_manager_testing_snapshots/one_line")


def test_one_line(tmp_path: str) -> None:
    manager = func_one_line(tmp_path)
    snapshot_count = manager.get_snapshot_count()
    # assert_output_files_match(snapshot_count, tmp_path.name, "snapshot_manager_testing_snapshots/one_line")
