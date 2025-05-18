"""Run from the `pyta` root directory to use the local `python_ta` rather than
installed `python_ta` package.
"""

import io
import os
import select
import signal
import subprocess
import sys
import time
from os import path, remove
from pathlib import Path
from subprocess import Popen

import pytest

import python_ta


def test_check_on_dir():
    """The function, check_all() should handle a top-level dir as input."""
    reporter = python_ta.check_all(
        "tests/fixtures/sample_dir",
        config={
            "output-format": "pyta-json",
            "pyta-error-permission": "no",
            "pyta-file-permission": "no",
        },
    )

    # get file names from sample_dir
    sample_files = []
    for _, _, files in os.walk("tests/fixtures/sample_dir"):
        for file in files:
            if file.lower().endswith(".py"):
                sample_files.append(file)

    for filename, messages in reporter.messages.items():
        assert "astroid-error" not in {
            msg.message.symbol for msg in messages
        }, f"astroid-error encountered for {filename}"
        name = os.path.basename(filename)
        assert name in sample_files, f"{name} not in sample_files"
        sample_files.remove(name)

    assert not sample_files, f"the following files not checked by python_ta: {sample_files}"


def test_check_on_file():
    """Test files"""
    _inputs = [["examples/nodes/name.py"], ["examples/nodes/dict.py", "examples/nodes/const.py"]]
    for item in _inputs:
        python_ta.check_all(
            item,
            config={
                "output-format": "pyta-plain",
                "pyta-error-permission": "no",
                "pyta-file-permission": "no",
            },
        )


def test_check_on_package():
    """Test inputs written in package notation."""
    _inputs = [
        ["examples.sample_usage.draw_cfg"],
        ["examples.sample_usage", "examples/nodes/const.py"],
    ]
    for item in _inputs:
        python_ta.check_all(
            item,
            output="pyta_output.html",
            config={
                "output-format": "pyta-plain",
                "pyta-error-permission": "no",
                "pyta-file-permission": "no",
            },
        )
    file_exists = path.exists("pyta_output.html")

    assert file_exists

    # If the file exists, the assertion passes and the file gets removed from the main directory
    if file_exists:
        remove("pyta_output.html")


def test_check_on_bad_input():
    """Test bad inputs. In all cases, pyta should recover.
    Any valid files, if any, should be checked.
    """
    _inputs = [
        [222],
        222,
        ["examples/nodes/dict.py examples/nodes/const.py"],
        [222, "examples/inline_config_comment.py", "examples/nodes/dict.py"],
        ["file_does_not_exist"],
        ["module_dne.file_dne"],
    ]
    for item in _inputs:
        python_ta.check_all(
            item,
            config={
                "output-format": "pyta-plain",
                "pyta-error-permission": "no",
                "pyta-file-permission": "no",
            },
        )


def test_check_with_config():
    """Test inputs along with a config arg."""
    _inputs = [["examples/nodes/const.py"], ["examples/nodes"]]
    CONFIG = {
        # [ELIF]
        "max-nested-blocks": 4,
        # [FORMAT]
        "max-line-length": 80,
        # [FORBIDDEN IMPORT]
        "allowed-import-modules": ["doctest", "unittest", "hypothesis", "python_ta"],
        # [FORBIDDEN IO]
        "allowed-io": [],
        # [MESSAGES CONTROL]
        "disable": [
            "R0401",
            "R0901",
            "R0903",
            "R0904",
            "R0911",
            "R0916",
            "W0402",
            "W0403",
            "W0410",
            "W1501",
            "W1502",
            "W1505",
            "E1300",
            "E1301",
            "E1302",
            "E1304",
            "W1300",
            "W1301",
            "W1302",
            "W1304",
            "E1124",
            "E1125",
            "E1129",
            "E1132",
            "W1402",
            "W0105",
            "E1303",
            "W1306",
            "W1307",
            "E0116",
            "E0114",
            "E0112",
            "E0115",
            "E0106",
            "E0113",
            "E0111",
            "E0105",
            "E0100",
            "E0117",
            "W0150",
            "W0120",
            "W0124",
            "W0108",
            "W0123",
            "W0122",
            "W0110",
            "C0122",
            "C0200",
            "W0141",
            "W0640",
            "W0623",
            "W0614",
            "W0604",
            "W0603",
            "W0602",
            "W0601",
            "E0604",
            "E0603",
            "E1200",
            "E1201",
            "E1202",
            "W1201",
            "E1205",
            "E1206",
            "similarities",
            "newstyle",
            "python3",
            "W0512",
            "C0403",
            "C0401",
            "C0402",
            "E1701",
            "E1700",
            "W0332",
            "C0327",
            "C0328",
            "E0202",
            "E0241",
            "E0704",
            "W0211",
            "W0232",
            "W0511",
            "R0204",
            "C0303",
            "W0231",
        ],
        # [CUSTOM PYTA OPTIONS]
        "output-format": "pyta-plain",
        "pyta-error-permission": "no",
        "pyta-file-permission": "no",
    }
    for item in _inputs:
        python_ta.check_all(item, config=CONFIG)


def test_check_saves_file() -> None:
    """Test whether or not specifiying an output properly saves a file"""
    _inputs = [["examples/nodes/name.py"]]
    for item in _inputs:
        # Note that the reporter output will be created in the main directory
        python_ta.check_all(item, output="pyta_output.html")

    file_exists = path.exists("pyta_output.html")

    assert file_exists

    # If the file exists, the assertion passes and the file gets removed from the main directory
    if file_exists:
        remove("pyta_output.html")


def test_check_no_reporter_output(prevent_webbrowser_and_httpserver) -> None:
    """Test whether not specifiying an output does not save a file"""
    _inputs = [["examples/nodes/name.py"]]
    for item in _inputs:
        # Note that the reporter output *would have been* created in the main directory
        python_ta.check_all(item)

    file_exists = path.exists("pyta_output.html")

    assert not file_exists

    # If the file exists, the assertion failed and the file gets removed from main directory
    if file_exists:
        remove("pyta_output.html")


def test_check_watch_enabled() -> None:
    """Test PythonTA's watch mode to ensure it detects changes correctly."""
    reset_watch_fixture()
    script_path = os.path.normpath(
        os.path.join(__file__, "../fixtures/sample_dir/watch/watch_enabled_configuration.py")
    )

    process = subprocess.Popen(
        [sys.executable, "-u", script_path],
        stdout=subprocess.PIPE,
        text=True,
    )

    try:
        lines = read_nonblocking(process, 6)
        assert any(
            "[Line 6] Incompatible types in assignment (expression has type str, variable has type int)"
            in line
            for line in lines
        )

        modify_watch_fixture()
        lines = read_nonblocking(process, 6)

        assert not any(
            "[Line 6] Incompatible types in assignment (expression has type str, variable has type int)"
            in line
            for line in lines
        )

    finally:
        process.terminate()
        process.wait()
        reset_watch_fixture()


def test_watch_output_file_appends(tmp_path: Path) -> None:
    """Test that using output=<file> with watch=True appends reports instead of overwriting."""
    output_file = tmp_path / "report_output.txt"
    script_path = os.path.normpath(
        os.path.join(__file__, "../fixtures/sample_dir/watch/watch_enabled_configuration.py")
    )

    reset_watch_fixture(str(output_file))
    process = subprocess.Popen(
        [sys.executable, "-u", script_path],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    try:
        if not wait_for_log_message(
            process, "PythonTA is monitoring your files for changes and will re-check", 10
        ):
            pytest.fail("Report did not generate within the expected timeout")

        detectedModification = False
        start = time.time()
        while not detectedModification and time.time() - start < 10:
            modify_watch_fixture(str(output_file))
            detectedModification = wait_for_file_response(output_file, 2)

        assert detectedModification, "Report did not generate within the expected timeout"
    finally:
        process.terminate()
        process.wait()
        reset_watch_fixture()


def wait_for_file_response(file_path: Path, timeout) -> bool:
    """Wait until the file exists and contains at least two instances of "PyTA Report for: <script_path>".
    Returns True if the content is found within the timeout, and False otherwise.
    """
    start = time.time()
    while time.time() - start < timeout:
        if os.path.exists(file_path):
            with open(file_path, "r", errors="ignore") as f:
                contents = f.read()
            if contents.count(f"PyTA Report for: ") >= 2:
                return True
    return False


def wait_for_log_message(process: subprocess.Popen, match: str, timeout: int) -> bool:
    """Wait until a specific line containing the given match string appears in the process's stderr.
    Returns True if the line is found within the timeout period, and False otherwise.
    """
    start = time.time()
    while time.time() - start < timeout:
        ready, _, _ = select.select([process.stderr], [], [], 0)
        if ready:
            line = process.stderr.readline()
            if match in line:
                return True
    return False


def reset_watch_fixture(output_path: str = None) -> None:
    """Reset the contents of watch_enabled_configuration.py to its original state."""
    output_arg = f', output="{output_path}"' if output_path else ""
    original_content = f'''"""This script serves as the entry point for an integration test of the _check watch mode."""\n
import python_ta

def blank_function() -> int:
    count: int = "ten"
    return count

if __name__ == "__main__":
    python_ta.check_all(config={{
        "output-format": "python_ta.reporters.PlainReporter",
        "watch": True
    }}{output_arg})
'''
    script_path = os.path.normpath(
        os.path.join(__file__, "../fixtures/sample_dir/watch/watch_enabled_configuration.py")
    )
    with open(script_path, "w") as file:
        file.write(original_content)


def modify_watch_fixture(output_path: str = None) -> None:
    """Modify the contents of watch_enabled_configuration.py to fix the type error."""
    output_arg = f', output="{output_path}"' if output_path else ""
    original_content = f'''"""This script serves as the entry point for an integration test of the _check watch mode."""\n
import python_ta

def blank_function() -> int:
    count: int = 10
    return count

if __name__ == "__main__":
    python_ta.check_all(config={{
        "output-format": "python_ta.reporters.PlainReporter",
        "watch": True
    }}{output_arg})
'''
    script_path = os.path.normpath(
        os.path.join(__file__, "../fixtures/sample_dir/watch/watch_enabled_configuration.py")
    )
    with open(script_path, "w") as file:
        file.write(original_content)


def read_nonblocking(process: Popen[str], timeout: int) -> list[str]:
    """Reads output from process without blocking until timeout or termination condition."""
    lines = []
    start_time = time.time()

    ready, _, _ = select.select([process.stdout], [], [], timeout)
    if ready:
        while True:
            line = process.stdout.readline().strip()
            lines.append(line)
            if (
                "=== Style/convention errors (fix: before submission) ===" in line
                or time.time() - start_time > timeout
            ):
                break
    return lines


@pytest.fixture
def output() -> None:
    """Create a StringIO object to be passed into the output argument of the check functions."""
    output = io.StringIO()
    yield output
    output.close()


def test_check_all_output_typing_io(output: io.StringIO) -> None:
    """Test that specifying output as a typing.IO stream captures the output report when check_all is called."""
    python_ta.check_all(
        "examples/custom_checkers/e9989_pep8_errors.py",
        config={"output-format": "pyta-plain"},
        output=output,
    )
    assert "E9989 (pep8-errors)" in output.getvalue()


def test_check_error_output_typing_io(output: io.StringIO) -> None:
    """Test that specifying output as a typing.IO stream captures the output report when check_error is called."""
    python_ta.check_errors(
        "examples/syntax_errors/missing_colon.py",
        config={"output-format": "pyta-plain"},
        output=output,
    )
    assert "E0001 (syntax-error)" in output.getvalue()


def test_precondition_inline_comment_no_error(caplog) -> None:
    """Test that no warnings are raised when inline comments are included in the preconditions
    of a function docstring.
    """
    python_ta.check_all(
        "tests/fixtures/precondition_inline_comment.py",
        config={"output-format": "python_ta.reporters.PlainReporter"},
    )

    assert "WARNING" not in [record.levelname for record in caplog.records]


def test_check_all_returns_max_messages_when_max_exceeded(capsys):
    """Test that check_all outputs only the max number of messages set when the max is exceeded."""

    python_ta.check_all(
        "tests/fixtures/unused_imports.py",
        config={
            "output-format": "pyta-plain",
            "pyta-number-of-messages": 2,
        },
    )

    output = capsys.readouterr().out

    # Check that the first two outputs should appear
    assert "[Line 3]" in output
    assert "[Line 4]" in output

    # Verify that the third import should NOT be present
    assert "[Line 5]" not in output

    # Trucation message indicating max messages should be present
    assert "First 2 shown" in output
