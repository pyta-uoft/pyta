from __future__ import annotations

import os.path

import pytest
from pytest_snapshot.plugin import Snapshot

from python_ta.debug import SnapshotManager

SNAPSHOT_DIR = os.path.join(
    os.path.dirname(os.path.realpath(__file__)), "snapshot_manager_testing_snapshots"
)
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


def assert_output_files_match(
    snapshot_count: int, output_path: str, snapshot: Snapshot, function_name: str
):
    actual_svgs = {}
    for i in range(snapshot_count):
        file_name = f"snapshot-{i}.svg"
        actual_file = os.path.join(output_path, file_name)
        with open(actual_file) as actual_file:
            actual_svg = actual_file.read()
            actual_svgs[file_name] = actual_svg
    snapshot.assert_match_dir(actual_svgs, function_name)


@pytest.mark.parametrize(
    "test_func", [func_one_line, func_multi_line, func_mutation, func_for_loop, func_while]
)
def test_snapshot_manger(test_func, snapshot):
    snapshot.snapshot_dir = SNAPSHOT_DIR
    actual_dir = os.path.join(TEST_RESULTS_DIR, test_func.__name__)
    os.makedirs(actual_dir, exist_ok=True)
    manager = test_func(actual_dir)
    assert_output_files_match(
        manager.get_snapshot_count(), actual_dir, snapshot, test_func.__name__
    )
