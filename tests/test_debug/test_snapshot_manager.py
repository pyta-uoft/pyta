import os.path
import shutil

import pytest

from python_ta.debug import SnapshotManager

SNAPSHOT_DIR = "snapshot_manager_testing_snapshots"
TEST_RESULTS_DIR = "/tmp/test_results"


def func_one_line(output_path=None) -> SnapshotManager:
    with SnapshotManager(output_filepath=output_path, include=("func_one_line",)) as manager:
        num = 123
    return manager


def func_multi_line(output_path=None) -> SnapshotManager:
    with SnapshotManager(output_filepath=output_path, include=("func_multi_line",)) as manager:
        num = 123
        some_string = "Hello, world"
        num2 = 321
        arr = [some_string, "string 123321"]
    return manager


def func_mutation(output_path=None) -> SnapshotManager:
    with SnapshotManager(output_filepath=output_path, include=("func_mutation",)) as manager:
        num = 123
        num = 321
    return manager


def func_for_loop(output_path=None) -> SnapshotManager:
    with SnapshotManager(output_filepath=output_path, include=("func_for_loop",)) as manager:
        nums = [1, 2, 3]
        for i in range(len(nums)):
            nums[i] = nums[i] + 1
    return manager


# TODO: we are taking a snapshot even for statements, clarify if this is necessary
def func_if_else(output_path=None) -> SnapshotManager:
    with SnapshotManager(output_filepath=output_path, include=("func_if_else",)) as manager:
        num = 10
        if num > 5:
            result = "greater"
        else:
            result = "lesser"
    return manager


def func_while(output_path=None) -> SnapshotManager:
    with SnapshotManager(output_filepath=output_path, include=("func_while",)) as manager:
        num = 0
        while num < 3:
            num += 1

    return manager


def assert_output_files_match(snapshot_count: int, output_path: str, expected_path: str):
    for i in range(snapshot_count):
        actual_file = os.path.join(output_path, f"snapshot-{i}.svg")
        expected_file = os.path.join(expected_path, f"snapshot-{i}.svg")
        with (
            open(actual_file) as actual_file,
            open(expected_file) as expected_file,
        ):
            actual_svg = actual_file.read()
            expected_svg = expected_file.read()
            assert actual_svg == expected_svg


@pytest.mark.parametrize(
    "test_func", [func_one_line, func_multi_line, func_mutation, func_for_loop, func_while]
)
# TODO: find a good way to take snapshots
def test_snapshot_manger(test_func):
    # set up to ensure the output dir exists
    save_snapshots = False

    actual_dir = os.path.join(TEST_RESULTS_DIR, test_func.__name__)
    os.makedirs(actual_dir, exist_ok=True)

    manager = test_func(actual_dir)

    expected_dir = os.path.join(SNAPSHOT_DIR, test_func.__name__)
    if save_snapshots:
        shutil.rmtree(expected_dir, ignore_errors=True)
        shutil.copytree(actual_dir, expected_dir, dirs_exist_ok=True)
    else:
        assert_output_files_match(manager.get_snapshot_count(), actual_dir, expected_dir)

    # clean up the test dir
    shutil.rmtree(actual_dir)
