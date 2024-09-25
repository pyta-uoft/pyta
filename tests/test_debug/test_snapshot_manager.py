from __future__ import annotations

import os.path
import shutil
import sys

import pytest
from pytest_snapshot.plugin import Snapshot

from python_ta.debug import SnapshotManager

SNAPSHOT_DIR = os.path.join(
    os.path.dirname(os.path.realpath(__file__)), "snapshot_manager_testing_snapshots"
)
TEST_RESULTS_DIR = "/tmp/test_results"


def func_one_line(output_path=None) -> None:
    with SnapshotManager(output_filepath=output_path, include=("func_one_line",)):
        num = 123


def func_multi_line(output_path=None) -> None:
    with SnapshotManager(output_filepath=output_path, include=("func_multi_line",)):
        num = 123
        some_string = "Hello, world"
        num2 = 321
        arr = [some_string, "string 123321"]


def func_mutation(output_path=None) -> None:
    with SnapshotManager(output_filepath=output_path, include=("func_mutation",)):
        num = 123
        num = 321


def func_for_loop(output_path=None) -> None:
    with SnapshotManager(output_filepath=output_path, include=("func_for_loop",)):
        nums = [1, 2, 3]
        for i in range(len(nums)):
            nums[i] = nums[i] + 1


def func_if_else(output_path=None) -> None:
    with SnapshotManager(output_filepath=output_path, include=("func_if_else",)):
        num = 10
        if num > 5:
            result = "greater"
        else:
            result = "lesser"


def func_while(output_path=None) -> None:
    with SnapshotManager(output_filepath=output_path, include=("func_while",)):
        num = 0
        while num < 3:
            num += 1


def assert_output_files_match(output_path: str, snapshot: Snapshot, function_name: str):
    actual_svgs = {}
    files = os.listdir(output_path)
    for file in files:
        actual_file = os.path.join(output_path, file)
        with open(actual_file) as actual_file:
            actual_svg = actual_file.read()
            actual_svgs[file] = actual_svg
    snapshot.assert_match_dir(actual_svgs, function_name)


@pytest.mark.skipif(sys.version_info < (3, 10), reason="requires Python 3.10 or higher")
@pytest.mark.parametrize(
    "test_func",
    [func_one_line, func_multi_line, func_mutation, func_for_loop, func_while, func_if_else],
)
def test_snapshot_manger(test_func, snapshot):
    snapshot.snapshot_dir = SNAPSHOT_DIR
    actual_dir = os.path.join(TEST_RESULTS_DIR, test_func.__name__)
    shutil.rmtree(actual_dir, ignore_errors=True)
    os.makedirs(actual_dir, exist_ok=True)

    test_func(actual_dir)

    assert_output_files_match(actual_dir, snapshot, test_func.__name__)
