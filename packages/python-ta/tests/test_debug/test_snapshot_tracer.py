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

from python_ta.debug import SnapshotTracer, run_with_snapshot_tracer

SNAPSHOT_DIR = os.path.join(
    os.path.dirname(os.path.realpath(__file__)), "snapshot_tracer_testing_snapshots"
)
MEMORY_VIZ_ARGS = ["--roughjs-config", "seed=12345"]
MEMORY_VIZ_VERSION = "0.5.0"
START = "# pyta: snapshot-tracer-start"
END = "# pyta: snapshot-tracer-end"


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


@pytest.mark.skipif(sys.version_info < (3, 10), reason="requires Python 3.10 or higher")
class TestRunWithSnapshotTracer:
    """
    Tests for run_with_snapshot_tracer. These tests are skipped if the Python version is less
    than 3.10.
    """

    def test_header_stays_outside_with_block(self, tmp_path):
        """
        Test that run_with_snapshot_tracer runs a file with a module docstring and several
        `from __future__` imports, which must come first in a module, and starts the code shown
        in the Webstepper after them.
        """
        path = tmp_path / "demo.py"
        path.write_text(
            '"""Docstring."""\n'
            "from __future__ import annotations\n"
            "from __future__ import division\n"
            "x = 1\n",
            encoding="utf-8",
        )

        tracer = run_with_snapshot_tracer(str(path), webstepper=False)

        assert tracer._get_code() == ("x = 1", 4)

    @pytest.mark.parametrize(
        "source, expected_code",
        [
            ("x = 1\ny = 2\n", ("x = 1\ny = 2", 1)),
            ('"""Multi-line\ndocstring."""\nx = 1\n', ("x = 1", 3)),
            (
                '"""Docstring."""\n\n@staticmethod\n@staticmethod\ndef f():\n    pass\nx = 1\n',
                ("@staticmethod\n@staticmethod\ndef f():\n    pass\nx = 1", 3),
            ),
        ],
    )
    def test_webstepper_code_starts_at_first_statement(self, tmp_path, source, expected_code):
        """
        Test that the code shown in the Webstepper starts at the first statement after the
        module header, including any decorators on that statement.
        """
        path = tmp_path / "demo.py"
        path.write_text(source, encoding="utf-8")

        tracer = run_with_snapshot_tracer(str(path), webstepper=False)

        assert tracer._get_code() == expected_code

    def test_webstepper_code_includes_lines_not_run(self, tmp_path):
        """
        Test that the code shown in the Webstepper includes the whole file, including a branch
        that is not run.
        """
        path = tmp_path / "demo.py"
        path.write_text("if True:\n    x = 1\nelse:\n    x = 2\n", encoding="utf-8")

        tracer = run_with_snapshot_tracer(str(path), webstepper=False)

        assert tracer._get_code() == ("if True:\n    x = 1\nelse:\n    x = 2", 1)

    def test_error_points_to_original_line(self, tmp_path):
        """
        Test that an error raised by the traced file is reported at the file's original path
        and line.
        """
        path = tmp_path / "demo.py"
        path.write_text('"""Docstring."""\nx = 1\nraise ValueError("error")\n', encoding="utf-8")

        with pytest.raises(ValueError) as exc_info:
            run_with_snapshot_tracer(str(path), webstepper=False)

        last_frame = exc_info.tb
        while last_frame.tb_next is not None:
            last_frame = last_frame.tb_next

        assert last_frame.tb_frame.f_code.co_filename == str(path)
        assert last_frame.tb_lineno == 3

    def test_runs_as_main(self, tmp_path):
        """
        Test that run_with_snapshot_tracer runs the file as the "__main__" module, so code in an
        `if __name__ == "__main__"` block is run and traced.
        """
        path = tmp_path / "demo.py"
        path.write_text('if __name__ == "__main__":\n    x = 1\n', encoding="utf-8")

        tracer = run_with_snapshot_tracer(str(path), webstepper=False)

        assert 2 in [snapshot_entry["lineNumber"] for snapshot_entry in tracer.snapshots]

    def test_webstepper_true_by_default(self, tmp_path):
        """
        Test that run_with_snapshot_tracer creates a SnapshotTracer that opens the Webstepper
        by default.
        """
        path = tmp_path / "demo.py"
        path.write_text("x = 1\n", encoding="utf-8")

        with patch("python_ta.debug.snapshot_tracer.SnapshotTracer") as mock_tracer:
            run_with_snapshot_tracer(str(path))

        mock_tracer.assert_called_once_with(webstepper=True)

    def test_kwargs_passed_to_snapshot_tracer(self, tmp_path):
        """
        Test that keyword arguments given to run_with_snapshot_tracer are passed to
        SnapshotTracer, including webstepper=False overriding the default.
        """
        path = tmp_path / "demo.py"
        path.write_text("x = 1\n", encoding="utf-8")

        with patch("python_ta.debug.snapshot_tracer.SnapshotTracer") as mock_tracer:
            run_with_snapshot_tracer(
                str(path), webstepper=False, include_frames=["f"], exclude_vars=["x"]
            )

        mock_tracer.assert_called_once_with(
            webstepper=False, include_frames=["f"], exclude_vars=["x"]
        )


@pytest.mark.skipif(sys.version_info < (3, 10), reason="requires Python 3.10 or higher")
class TestSnapshotTracerComments:
    """
    Tests for the "# pyta: snapshot-tracer-start" and "# pyta: snapshot-tracer-end" comments
    used by run_with_snapshot_tracer. These tests are skipped if the Python version is less
    than 3.10.
    """

    # The start comment's line is traced too: the `with` block that replaces the marked
    # statements is placed on that line, and takes a snapshot there when it exits.
    @pytest.mark.parametrize(
        "source, expected_code, expected_lines",
        [
            # A block at the module level
            (
                f"x = 1\n{START}\ny = 2\nz = 3\n{END}\nw = 4\n",
                ("y = 2\nz = 3", 3),
                {2, 3, 4},
            ),
            # A block inside a function body, with a branch that is not run
            (
                f"def f(n):\n    a = 1\n    {START}\n    if n <= 0:\n        x = 1\n    else:\n"
                f"        x = 3\n    {END}\n    return x\nf(0)\n",
                ("    if n <= 0:\n        x = 1\n    else:\n        x = 3", 4),
                {3, 4, 5},
            ),
            # A block starting with a decorated function
            (
                f"import functools\n{START}\n@functools.cache\ndef g():\n"
                f"    return 1\ng()\n{END}\nh = 1\n",
                ("@functools.cache\ndef g():\n    return 1\ng()", 3),
                {2, 3, 4, 5, 6},
            ),
            # Only the first start comment and the first end comment after it are used
            (
                f"{END}\na = 1\n{START}\nb = 2\n{END}\nc = 3\n{START}\nd = 4\n{END}\n",
                ("b = 2", 4),
                {3, 4},
            ),
            # Blank lines, other comments and a semicolon in the block
            (
                f"{START}\n\n# comment\na = 1;\n\n{END}\nb = 2\n",
                ("\n# comment\na = 1;", 2),
                {1, 4},
            ),
        ],
    )
    def test_traces_only_marked_block(self, tmp_path, source, expected_code, expected_lines):
        """
        Test that exactly the statements between the snapshot-tracer comments are traced, and
        that the code shown in the Webstepper is the whole marked block, including lines that
        are not run.

        Traced lines are compared as a set because the order and repeats of line events
        differ between Python versions (e.g., for decorators).
        """
        path = tmp_path / "demo.py"
        path.write_text(source, encoding="utf-8")

        tracer = run_with_snapshot_tracer(str(path), webstepper=False)

        traced_lines = {snapshot_entry["lineNumber"] for snapshot_entry in tracer.snapshots}
        assert tracer._get_code() == expected_code
        assert traced_lines == expected_lines

    def test_empty_block_traces_nothing(self, tmp_path):
        """
        Test that the file runs without tracing anything when there is no code between the
        snapshot-tracer comments.
        """
        path = tmp_path / "demo.py"
        path.write_text(f"a = 1\n{START}\n\n# comment\n{END}\n", encoding="utf-8")

        tracer = run_with_snapshot_tracer(str(path), webstepper=False)

        assert tracer.snapshots == []

    @pytest.mark.parametrize(
        "source, message, line",
        [
            (f"a = 1  {START}\n{END}\n", "on a line by itself", 1),
            (f"{START}\na = 1\n", "has no matching snapshot-tracer-end", 1),
            (f"a = 1\n{END}\n", "has no matching snapshot-tracer-start", 2),
            # A start comment before an `else:`
            (
                f"if True:\n    a = 1\n{START}\nelse:\n    b = 1\n{END}\n",
                "must be directly followed by a statement",
                3,
            ),
            # An end comment in the `else` branch of the start comment's `if`
            (
                f"if True:\n    {START}\n    a = 1\nelse:\n    {END}\n    b = 1\n",
                "must be in the same block",
                5,
            ),
            # An end comment after a complete statement in a different block
            (
                f"def f():\n    {START}\n    a = 1\nb = 2\n{END}\n",
                "must be in the same block",
                5,
            ),
        ],
    )
    def test_invalid_comments_raise(self, tmp_path, source, message, line):
        """
        Test that snapshot-tracer comments that do not mark a block of statements raise a
        SyntaxError pointing at the comment at fault.
        """
        path = tmp_path / "demo.py"
        path.write_text(source, encoding="utf-8")

        with pytest.raises(SyntaxError, match=message) as exc_info:
            run_with_snapshot_tracer(str(path), webstepper=False)

        assert exc_info.value.filename == str(path)
        assert exc_info.value.lineno == line
