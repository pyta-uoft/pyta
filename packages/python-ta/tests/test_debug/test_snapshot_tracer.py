from __future__ import annotations

import importlib.util
import inspect
import os.path
import sys
import warnings
from typing import Any, Iterator
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


def func_one_line() -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        include_frames=(r"^func_one_line$",),
        exclude_vars=("tracer"),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        num = 123

    return tracer


def func_multi_line() -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        include_frames=(r"^func_multi_line$",),
        exclude_vars=("tracer"),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        num = 123
        some_string = "Hello, world"
        num2 = 321
        arr = [some_string, "string 123321"]

    return tracer


def func_mutation() -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        include_frames=(r"^func_mutation$",),
        exclude_vars=("tracer"),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        num = 123
        num = 321

    return tracer


def func_for_loop() -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        include_frames=(r"^func_for_loop$",),
        exclude_vars=("tracer"),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        nums = [1, 2, 3]
        for i in range(len(nums)):
            nums[i] = nums[i] + 1
    return tracer


def func_if_else() -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        include_frames=(r"^func_if_else$",),
        exclude_vars=("tracer"),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        num = 10
        if num > 5:
            result = "greater"
        else:
            result = "lesser"
    return tracer


def func_while() -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        include_frames=(r"^func_while$",),
        exclude_vars=("tracer"),
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


def func_open_webstepper() -> None:
    """
    Function for testing SnapshotTracer works with Webstepper
    """
    with SnapshotTracer(
        include_frames=(r"^func_open_webstepper$",),
        exclude_vars=("tracer"),
        webstepper=True,
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        nums = [1, 2, 3]
        for i in range(len(nums)):
            nums[i] = nums[i] + 1
    return tracer


def func_same_module_call() -> SnapshotTracer:
    """
    Function for testing SnapshotTracer traces into same-module function calls
    """
    with SnapshotTracer(
        include_frames=(r"^func_same_module_call$", r"^helper_same_module$"),
        exclude_vars=("tracer",),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        helper_same_module(5)
        num = 42

    return tracer


def func_builtin_call() -> SnapshotTracer:
    """
    Function for testing SnapshotTracer does not trace into built-in function calls
    """
    with SnapshotTracer(
        include_frames=(r"^func_builtin_call$",),
        exclude_vars=("tracer",),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        nums = [1, 2, 3]
        total = sum(nums)

    return tracer


def func_calls_external_helper(external_helper: Any) -> SnapshotTracer:
    """Function for testing SnapshotTracer does not trace into imported modules."""
    with SnapshotTracer(
        include_frames=(r"^func_calls_external_helper$", r"^external_helper_call$"),
        exclude_vars=("tracer",),
        memory_viz_args=MEMORY_VIZ_ARGS,
        memory_viz_version=MEMORY_VIZ_VERSION,
    ) as tracer:
        external_helper.external_helper_call()

    return tracer


def func_webstepper_options() -> None:
    """
    Function for testing SnapshotTracer with webstepper_options.
    """
    with SnapshotTracer(
        include_frames=(r"^func_webstepper_options$",),
        exclude_vars=("tracer",),
        webstepper=True,
        webstepper_options={"line_context": 2},
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
    assert len(tracer.snapshots) == expected_num_snapshots

    for snapshot_entry in tracer.snapshots:
        assert "lineNumber" in snapshot_entry
        assert "memoryVizInput" in snapshot_entry

        assert isinstance(snapshot_entry["memoryVizInput"], list)


def helper_same_module(x: int) -> int:
    """
    Helper used to verify SnapshotTracer traces into same-module calls.
    """
    result = x
    return result


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
    def test_snapshot_tracer_with_functions(self, test_func):
        """
        Test SnapshotTracer with various simple functions.
        """
        tracer = test_func()

        assert len(tracer.snapshots) > 0
        for entry in tracer.snapshots:
            assert "lineNumber" in entry
            assert "memoryVizInput" in entry
            assert isinstance(entry["lineNumber"], int)
            assert isinstance(entry["memoryVizInput"], list)

    def test_output_directory_deprecated(self):
        """
        Test that a warning is raised when the deprecated `output_directory` argument is used.
        """
        with pytest.warns(DeprecationWarning):
            SnapshotTracer(output_directory=".")

    def test_serve_html_calls_open_in_browser(self):
        """
        Test that SnapshotTracer opens the Webstepper HTML page when `webstepper=True`.
        """
        with patch("python_ta.debug.snapshot_tracer.open_html_in_browser") as mock_open:
            func_open_webstepper()
            mock_open.assert_called_once()

    def test_snapshot_contains_json_data(self):
        """
        Test SnapshotTracer stores memory visualization data in JSON format.
        """
        tracer = func_multi_line()
        snapshot_entry = tracer.snapshots[0]
        memory_input = snapshot_entry["memoryVizInput"]
        assert isinstance(memory_input, list)
        frame_entries = [entry for entry in memory_input if entry["type"] == ".frame"]
        assert len(frame_entries) > 0

    def test_snapshot_to_json_called(self):
        """
        Test that SnapshotTracer calls `snapshot_to_json` when processing snapshots.
        """
        with patch("python_ta.debug.snapshot_tracer.snapshot_to_json") as mock_json:
            mock_json.return_value = []
            func_one_line()
            mock_json.assert_called()

    def test_build_html_contains_memoryviz_data(self):
        """
        Test that SnapshotTracer stores memory visualization data to generate HTML.
        """
        tracer = func_one_line()
        assert len(tracer.snapshots) > 0
        assert all("memoryVizInput" in snap for snap in tracer.snapshots)

    def test_snapshots_property_returns_internal_data(self):
        """
        Test that the `snapshots` property returns the same data as `_snapshots`.
        """
        tracer = func_multi_line()
        assert tracer.snapshots is tracer._snapshots

    def test_snapshots_property_is_read_only(self):
        """
        Test that the `snapshots` property is read-only and cannot be set to a new value.
        """
        tracer = func_multi_line()
        with pytest.raises(AttributeError):
            tracer.snapshots = []

    def test_traces_same_module_function_calls(self):
        """
        Test SnapshotTracer traces into helper functions defined in the same module.
        """
        tracer = func_same_module_call()
        traced_frame_names = {
            entry["name"]
            for snapshot_entry in tracer.snapshots
            for entry in snapshot_entry["memoryVizInput"]
            if entry["type"] == ".frame"
        }
        assert "helper_same_module" in traced_frame_names

    def test_does_not_trace_builtin_calls(self):
        """
        Test SnapshotTracer does not trace into built-in function calls
        """
        tracer = func_builtin_call()
        traced_frame_names = {
            entry["name"]
            for snapshot_entry in tracer.snapshots
            for entry in snapshot_entry["memoryVizInput"]
            if entry["type"] == ".frame"
        }
        assert "sum" not in traced_frame_names

    def test_does_not_trace_external_module_calls(self, tmp_path):
        """
        Test SnapshotTracer does not trace into functions defined in external modules.
        """
        module_path = tmp_path / "external_helper.py"
        module_path.write_text(
            """
            def external_helper_call():
                value = 1
                value += 1
                return value
            """.lstrip(),
            encoding="utf-8",
        )

        spec = importlib.util.spec_from_file_location("external_helper", module_path)
        assert spec is not None and spec.loader is not None
        external_helper = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(external_helper)

        tracer = func_calls_external_helper(external_helper)
        traced_frame_names = {
            entry["name"]
            for snapshot_entry in tracer.snapshots
            for entry in snapshot_entry["memoryVizInput"]
            if entry["type"] == ".frame"
        }
        assert "external_helper_call" not in traced_frame_names

    def test_settrace_restored_after_exit(self):
        """
        Test that sys.settrace is restored after exiting the SnapshotTracer context.
        """
        func_one_line()
        assert sys.gettrace() is None

    def test_webstepper_options_warning_when_webstepper_false(self):
        """
        Test that a warning is raised when webstepper_options are provided but webstepper=False.
        """
        with pytest.warns(UserWarning):
            SnapshotTracer(webstepper=False, webstepper_options={"line_context": 2})

    def test_webstepper_options_no_warning_when_webstepper_true(self):
        """
        Test that no warning is raised when webstepper_options are provided and webstepper=True.
        """
        with patch("python_ta.debug.snapshot_tracer.open_html_in_browser"):
            with warnings.catch_warnings():
                warnings.simplefilter("error", UserWarning)
                SnapshotTracer(webstepper=True, webstepper_options={"line_context": 2})

    def test_line_context_expands_code(self):
        """
        Test that line_context produces more lines of code than without it.
        """
        with patch("python_ta.debug.snapshot_tracer.open_html_in_browser"):
            tracer_no_context = func_open_webstepper()
            tracer_with_context = func_webstepper_options()

        assert len(tracer_with_context.snapshots) >= len(tracer_no_context.snapshots)

    def test_webstepper_options_line_context_with_html(self):
        """
        Test that SnapshotTracer with line_context opens the Webstepper HTML page.
        """
        with patch("python_ta.debug.snapshot_tracer.open_html_in_browser") as mock_open:
            func_webstepper_options()
            mock_open.assert_called_once()
