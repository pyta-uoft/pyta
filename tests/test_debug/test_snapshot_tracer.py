from __future__ import annotations

import os.path
import shutil
import sys
from typing import Iterator

import pytest
from pytest_snapshot.plugin import Snapshot

from python_ta.debug import SnapshotTracer

SNAPSHOT_DIR = os.path.join(
    os.path.dirname(os.path.realpath(__file__)), "snapshot_tracer_testing_snapshots"
)
TEST_RESULTS_DIR = "/tmp/test_results"
MEMORY_VIZ_ARGS = ["--roughjs-config", "seed=12345"]


# Function inputs for testing the SnapshotTracer


def func_one_line(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include=("func_one_line",),
        memory_viz_args=MEMORY_VIZ_ARGS,
    ):
        num = 123


def func_multi_line(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include=("func_multi_line",),
        memory_viz_args=MEMORY_VIZ_ARGS,
    ):
        num = 123
        some_string = "Hello, world"
        num2 = 321
        arr = [some_string, "string 123321"]


def func_mutation(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include=("func_mutation",),
        memory_viz_args=MEMORY_VIZ_ARGS,
    ):
        num = 123
        num = 321


def func_for_loop(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include=("func_for_loop",),
        memory_viz_args=MEMORY_VIZ_ARGS,
    ):
        nums = [1, 2, 3]
        for i in range(len(nums)):
            nums[i] = nums[i] + 1


def func_if_else(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include=("func_if_else",),
        memory_viz_args=MEMORY_VIZ_ARGS,
    ):
        num = 10
        if num > 5:
            result = "greater"
        else:
            result = "lesser"


def func_while(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory, include=("func_while",), memory_viz_args=MEMORY_VIZ_ARGS
    ):
        num = 0
        while num < 3:
            num += 1


def func_with_args() -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(include=("func_with_args",), memory_viz_args=MEMORY_VIZ_ARGS):
        flag = "not --output"


def func_no_memory_viz_args() -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(include=("func_no_memory_viz_args",), memory_viz_args=MEMORY_VIZ_ARGS):
        s = "Hello"


# Helpers


def assert_output_files_match(
    output_directory: str, snapshot: Snapshot, function_name: str
) -> None:
    """
    Assert that the output files in the output directory match the expected output.
    """
    actual_svgs = {}
    files = os.listdir(output_directory)
    for file in files:
        actual_path = os.path.join(output_directory, file)
        with open(actual_path) as actual_file:
            actual_svg = actual_file.read()
            actual_svgs[file] = actual_svg
    snapshot.assert_match_dir(actual_svgs, function_name)


# Fixtures


@pytest.fixture(scope="function")
def test_directory(test_func, snapshot) -> Iterator[str]:
    """
    Set up and tear down the test directory for the SnapshotTracer tests.
    """
    snapshot.snapshot_dir = SNAPSHOT_DIR
    actual_dir = os.path.join(TEST_RESULTS_DIR, test_func.__name__)
    shutil.rmtree(actual_dir, ignore_errors=True)
    os.makedirs(actual_dir, exist_ok=True)
    yield actual_dir
    shutil.rmtree(actual_dir, ignore_errors=True)


@pytest.fixture(scope="function")
def setup_curr_dir_testing(snapshot) -> Iterator[None]:
    """
    Set up and tear down the current directory for the SnapshotTracer tests.
    """
    snapshot.snapshot_dir = SNAPSHOT_DIR
    file_name = "snapshot-0.svg"
    if os.path.exists(file_name):
        os.remove(file_name)
    yield
    os.remove(file_name)


# Tests


@pytest.mark.skipif(sys.version_info < (3, 10), reason="requires Python 3.10 or higher")
class TestSnapshotTracer:
    """
    Tests for SnapshotTracer. These tests are skipped if the Python version is less than 3.10.
    """

    @pytest.mark.parametrize(
        "test_func",
        [
            func_one_line,
            func_multi_line,
            func_mutation,
            func_for_loop,
            func_while,
            func_if_else,
        ],
    )
    def test_snapshot_tracer_with_functions(self, test_func, snapshot, test_directory):
        """
        Test SnapshotTracer with various simple functions.
        """
        test_func(test_directory)

        assert_output_files_match(test_directory, snapshot, test_func.__name__)

    def test_func_with_non_output_flags(self, snapshot, setup_curr_dir_testing):
        """
        Test SnapshotTracer outputs to the current directory when `memory_viz_args` are passed.
        """
        func_with_args()

        with open("snapshot-0.svg") as actual_file:
            snapshot.assert_match_dir(
                {"snapshot-0.svg": actual_file.read()}, func_with_args.__name__
            )

    def test_using_output_flag(self):
        """
        Test SnapshotTracer raises an error when the `memory_viz_args` includes the `--output` flag.
        """
        with pytest.raises(
            ValueError,
            match="Use the output_directory parameter to specify a different output path.",
        ):
            with SnapshotTracer(
                include=("func_duplicate_output_path",), memory_viz_args=["--output", "."]
            ):
                pass

    def test_no_output_directory(self, snapshot, setup_curr_dir_testing):
        """
        Test SnapshotTracer outputs to the current directory when `output_directory` is not specified.
        """
        func_no_memory_viz_args()

        with open("snapshot-0.svg") as actual_file:
            snapshot.assert_match_dir(
                {"snapshot-0.svg": actual_file.read()}, func_no_memory_viz_args.__name__
            )
