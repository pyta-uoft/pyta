from __future__ import annotations

import inspect
import os.path
import sys
from typing import Iterator
from unittest.mock import patch

import pytest
from pytest_snapshot.plugin import Snapshot

from python_ta.debug import SnapshotTracer

SNAPSHOT_DIR = os.path.join(
    os.path.dirname(os.path.realpath(__file__)), "snapshot_tracer_testing_snapshots"
)
MEMORY_VIZ_ARGS = ["--roughjs-config", "seed=12345"]
MEMORY_VIZ_VERSION = "0.5.0"


# Function inputs for testing the SnapshotTracer


def func_one_line(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include_frames=(r"^func_one_line$",),
        exclude_vars=("output_directory", "tracer"),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        num = 123

    return tracer


def func_multi_line(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include_frames=(r"^func_multi_line$",),
        exclude_vars=("output_directory", "tracer"),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        num = 123
        some_string = "Hello, world"
        num2 = 321
        arr = [some_string, "string 123321"]

    return tracer


def func_mutation(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include_frames=(r"^func_mutation$",),
        exclude_vars=("output_directory", "tracer"),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        num = 123
        num = 321

    return tracer


def func_for_loop(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include_frames=(r"^func_for_loop$",),
        exclude_vars=("output_directory", "tracer"),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        nums = [1, 2, 3]
        for i in range(len(nums)):
            nums[i] = nums[i] + 1
    return tracer


def func_if_else(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include_frames=(r"^func_if_else$",),
        exclude_vars=("output_directory", "tracer"),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        num = 10
        if num > 5:
            result = "greater"
        else:
            result = "lesser"
    return tracer


def func_while(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include_frames=(r"^func_while$",),
        exclude_vars=("output_directory", "tracer"),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        num = 0
        while num < 3:
            num += 1
    return tracer


def func_no_output_dir() -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        include_frames=(r"^func_no_output_dir$",),
        exclude_vars=("tracer",),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        s = "Hello"
    return tracer


def func_open_webstepper(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer works with Webstepper
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include_frames=(r"^func_open_webstepper$",),
        exclude_vars=("output_directory", "tracer"),
        webstepper=True,
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        nums = [1, 2, 3]
        for i in range(len(nums)):
            nums[i] = nums[i] + 1
    return tracer


# Helpers


def assert_snapshot_data(
    tracer: SnapshotTracer,
    expected_num_snapshots: int,
) -> None:
    """
    Assert that SnapshotTracer stored JSON snapshot data correctly.
    """
    assert len(tracer._snapshots) == expected_num_snapshots

    for snapshot_entry in tracer._snapshots:
        assert "lineNumber" in snapshot_entry
        assert "memoryVizInput" in snapshot_entry

        assert isinstance(snapshot_entry["memoryVizInput"], list)


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
    def test_snapshot_tracer_with_functions(self, test_func, snapshot, tmp_path):
        """
        Test SnapshotTracer with various simple functions.
        """
        tracer = test_func(str(tmp_path))

        assert len(tracer._snapshots) > 0
        for entry in tracer._snapshots:
            assert "lineNumber" in entry
            assert "memoryVizInput" in entry
            assert isinstance(entry["lineNumber"], int)
            assert isinstance(entry["memoryVizInput"], list)

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

    def test_no_output_directory(self):
        """
        Test SnapshotTracer outputs to the current directory when `output_directory` is not specified.
        """
        tracer = func_no_output_dir()
        assert len(tracer._snapshots) > 0

    def test_serve_html_calls_open_in_browser(self):
        with patch("python_ta.debug.snapshot_tracer.open_html_in_browser") as mock_open:
            func_open_webstepper()
            mock_open.assert_called_once()

    def test_snapshot_contains_json_data(self, tmp_path):
        tracer = func_multi_line(str(tmp_path))
        snapshot_entry = tracer._snapshots[0]
        memory_input = snapshot_entry["memoryVizInput"]
        assert isinstance(memory_input, list)
        frame_entries = [entry for entry in memory_input if entry["type"] == ".frame"]
        assert len(frame_entries) > 0

    def test_snapshot_to_json_called(self, tmp_path):
        with patch("python_ta.debug.snapshot_tracer.snapshot_to_json") as mock_json:
            mock_json.return_value = []
            func_one_line(str(tmp_path))
            mock_json.assert_called()

    def test_build_html_contains_memoryviz_data(self, tmp_path):
        tracer = func_one_line(str(tmp_path))
        assert len(tracer._snapshots) > 0
        assert all("memoryVizInput" in snap for snap in tracer._snapshots)
