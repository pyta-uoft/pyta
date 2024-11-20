from __future__ import annotations

import os.path
import re
import sys
from typing import Iterator

import pytest
from pytest_snapshot.plugin import Snapshot

from python_ta.debug import SnapshotTracer

SNAPSHOT_DIR = os.path.join(
    os.path.dirname(os.path.realpath(__file__)), "snapshot_tracer_testing_snapshots"
)
MEMORY_VIZ_ARGS = ["--roughjs-config", "seed=12345"]
MEMORY_VIZ_VERSION = "0.4.0"


# Function inputs for testing the SnapshotTracer


def func_one_line(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include_frames=(r"^func_one_line$",),
        exclude_vars=("output_directory",),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ):
        num = 123


def func_multi_line(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include_frames=(r"^func_multi_line$",),
        exclude_vars=("output_directory",),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
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
        include_frames=(r"^func_mutation$",),
        exclude_vars=("output_directory",),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ):
        num = 123
        num = 321


def func_for_loop(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include_frames=(r"^func_for_loop$",),
        exclude_vars=("output_directory",),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
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
        include_frames=(r"^func_if_else$",),
        exclude_vars=("output_directory",),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
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
        output_directory=output_directory,
        include_frames=(r"^func_while$",),
        exclude_vars=("output_directory",),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ):
        num = 0
        while num < 3:
            num += 1


def func_no_output_dir() -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        include_frames=(r"^func_no_output_dir$",),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ):
        s = "Hello"


def func_open_webstepper(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer works with Webstepper
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include_frames=(r"^func_open_webstepper$",),
        exclude_vars=("output_directory",),
        open_webstepper=True,
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ):
        nums = [1, 2, 3]
        for i in range(len(nums)):
            nums[i] = nums[i] + 1


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
def setup_curr_dir_testing(snapshot: Snapshot) -> Iterator[None]:
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
            func_open_webstepper,
        ],
    )
    def test_snapshot_tracer_with_functions(self, test_func, snapshot, tmp_path):
        """
        Test SnapshotTracer with various simple functions.
        """
        snapshot.snapshot_dir = SNAPSHOT_DIR

        test_func(str(tmp_path))

        assert_output_files_match(str(tmp_path), snapshot, test_func.__name__)

    def test_using_output_flag(self):
        """
        Test SnapshotTracer raises an error when the `memory_viz_args` include_framess the `--output` flag.
        """
        with pytest.raises(
            ValueError,
            match="Use the output_directory parameter to specify a different output path.",
        ):
            with SnapshotTracer(
                include_frames=("func_duplicate_output_path",),
                memory_viz_args=["--output", "."],
                memory_viz_version=MEMORY_VIZ_VERSION,
            ):
                pass

    def test_no_output_directory(self, snapshot, setup_curr_dir_testing):
        """
        Test SnapshotTracer outputs to the current directory when `output_directory` is not specified.
        """
        func_no_output_dir()

        with open("snapshot-0.svg") as actual_file:
            snapshot.assert_match_dir(
                {"snapshot-0.svg": actual_file.read()}, func_no_output_dir.__name__
            )

    def test_generated_webstepper_html(self, snapshot, tmp_path):
        """
        Test SnapshotTracer generates the correct Webstepper html for the given code
        """
        snapshot.snapshot_dir = SNAPSHOT_DIR
        func_open_webstepper(str(tmp_path))

        index_path = os.path.join(str(tmp_path), "index.html")
        with open(index_path, "r+") as file:
            html_content = file.read()

            constant_js_src = "absolute/path/to/index.bundle.js"
            html_content = re.sub(
                r'(<script\s+defer="defer"\s+src=")[^"]*(")',
                r"\1" + constant_js_src + r"\2",
                html_content,
            )

            file.seek(0)
            file.write(html_content)
            file.truncate()

        assert_output_files_match(str(tmp_path), snapshot, func_open_webstepper.__name__)
