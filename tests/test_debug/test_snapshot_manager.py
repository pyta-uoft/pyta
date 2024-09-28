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
    with SnapshotManager(output_directory=output_path, include=("func_one_line",)):
        num = 123


def func_multi_line(output_path=None) -> None:
    with SnapshotManager(output_directory=output_path, include=("func_multi_line",)):
        num = 123
        some_string = "Hello, world"
        num2 = 321
        arr = [some_string, "string 123321"]


def func_mutation(output_path=None) -> None:
    with SnapshotManager(output_directory=output_path, include=("func_mutation",)):
        num = 123
        num = 321


def func_for_loop(output_path=None) -> None:
    with SnapshotManager(output_directory=output_path, include=("func_for_loop",)):
        nums = [1, 2, 3]
        for i in range(len(nums)):
            nums[i] = nums[i] + 1


def func_if_else(output_path=None) -> None:
    with SnapshotManager(output_directory=output_path, include=("func_if_else",)):
        num = 10
        if num > 5:
            result = "greater"
        else:
            result = "lesser"


def func_while(output_path=None) -> None:
    with SnapshotManager(output_directory=output_path, include=("func_while",)):
        num = 0
        while num < 3:
            num += 1


def func_with_args():
    with SnapshotManager(
        include=("func_with_args",), memory_viz_args=["--roughjs-config", "seed=12345"]
    ):
        flag = "not --output"


def assert_output_files_match(output_path: str, snapshot: Snapshot, function_name: str):
    actual_svgs = {}
    files = os.listdir(output_path)
    for file in files:
        actual_path = os.path.join(output_path, file)
        with open(actual_path) as actual_file:
            actual_svg = actual_file.read()
            actual_svgs[file] = actual_svg
    snapshot.assert_match_dir(actual_svgs, function_name)


def func_no_memory_viz_args():
    with SnapshotManager(include=("func_no_memory_viz_args",)):
        s = "Hello"


@pytest.fixture(scope="function")
def test_directory(func_name, snapshot):
    snapshot.snapshot_dir = SNAPSHOT_DIR
    actual_dir = os.path.join(TEST_RESULTS_DIR, func_name)
    shutil.rmtree(actual_dir, ignore_errors=True)
    os.makedirs(actual_dir, exist_ok=True)
    yield actual_dir
    shutil.rmtree(actual_dir, ignore_errors=True)


@pytest.fixture(scope="function")
def setup_curr_dir_testing(snapshot):
    snapshot.snapshot_dir = SNAPSHOT_DIR
    file_name = "snapshot-0.svg"
    if os.path.exists(file_name):
        os.remove(file_name)
    yield
    os.remove(file_name)


@pytest.mark.skipif(sys.version_info < (3, 10), reason="requires Python 3.10 or higher")
def test_func_with_non_output_flags(snapshot, setup_curr_dir_testing):
    func_with_args()

    with open("snapshot-0.svg") as actual_file:
        snapshot.assert_match_dir({"snapshot-0.svg": actual_file.read()}, func_with_args.__name__)


functions_to_test = [
    func_one_line,
    func_multi_line,
    func_mutation,
    func_for_loop,
    func_while,
    func_if_else,
]
func_with_names = [(func, func.__name__) for func in functions_to_test]


@pytest.mark.skipif(sys.version_info < (3, 10), reason="requires Python 3.10 or higher")
@pytest.mark.parametrize(
    "test_func,func_name",
    func_with_names,
)
def test_snapshot_manger_with_functions(test_func, snapshot, test_directory):
    test_func(test_directory)

    assert_output_files_match(test_directory, snapshot, test_func.__name__)


@pytest.mark.skipif(sys.version_info < (3, 10), reason="requires Python 3.10 or higher")
def test_outputs_to_default_directory_with_no_memory_viz_args(snapshot, setup_curr_dir_testing):
    func_no_memory_viz_args()

    with open("snapshot-0.svg") as actual_file:
        snapshot.assert_match_dir(
            {"snapshot-0.svg": actual_file.read()}, func_no_memory_viz_args.__name__
        )


@pytest.mark.skipif(sys.version_info < (3, 10), reason="requires Python 3.10 or higher")
def test_using_output_flag():
    with pytest.raises(
        ValueError, match="Use the output_directory argument to specify a different output path."
    ):
        with SnapshotManager(
            include=("func_duplicate_output_path",), memory_viz_args=["--output", "."]
        ):
            pass
