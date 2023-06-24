"""Run from the `pyta` root directory to use the local `python_ta` rather than
installed `python_ta` package.
"""
import subprocess
import sys
from os import path, remove
from unittest.mock import Mock

import python_ta


def test_check_on_dir():
    """The function, check_all() should handle a top-level dir as input."""
    reporter = python_ta.check_all(
        "examples",
        config={
            "output-format": "python_ta.reporters.JSONReporter",
            "pyta-error-permission": "no",
            "pyta-file-permission": "no",
        },
    )
    for filename, messages in reporter.messages.items():
        assert "astroid-error" not in {
            msg.message.symbol for msg in messages
        }, f"astroid-error encountered for {filename}"


def test_check_on_file():
    """Test files"""
    _inputs = [["examples/nodes/name.py"], ["examples/nodes/dict.py", "examples/nodes/const.py"]]
    for item in _inputs:
        python_ta.check_all(
            item,
            config={
                "output-format": "python_ta.reporters.PlainReporter",
                "pyta-error-permission": "no",
                "pyta-file-permission": "no",
            },
        )


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
    ]
    for item in _inputs:
        python_ta.check_all(
            item,
            config={
                "output-format": "python_ta.reporters.PlainReporter",
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
        "output-format": "python_ta.reporters.PlainReporter",
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


def test_check_no_reporter_output() -> None:
    """Test whether not specifiying an output does not save a file"""
    # To prevent any any browser/server code running when running Pytest to avoid CI timeouts
    import webbrowser
    from http.server import HTTPServer

    webbrowser.open = Mock(return_value=None)
    HTTPServer.handle_request = Mock(return_value=None)

    _inputs = [["examples/nodes/name.py"]]
    for item in _inputs:
        # Note that the reporter output *would have been* created in the main directory
        python_ta.check_all(item)

    file_exists = path.exists("pyta_output.html")

    assert not file_exists

    # If the file exists, the assertion failed and the file gets removed from main directory
    if file_exists:
        remove("pyta_output.html")


def test_check_no_errors_zero() -> None:
    """Test that python_ta exits with status code 0 when it does not detect errors."""
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            "tests/test.pylintrc",
            "tests/fixtures/no_errors.py",
        ]
    )

    assert output.returncode == 0


def test_check_errors_nonzero() -> None:
    """Test that python_ta exits with non-zero status code when it detects errors."""
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            "tests/test.pylintrc",
            "examples/nodes/name.py",
        ]
    )

    assert output.returncode != 0


def test_check_exit_zero() -> None:
    """Test that python_ta --exit-zero always exits with status code 0,
    even when given a file with errors.
    """
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--exit-zero",
            "--config",
            "tests/test.pylintrc",
            "examples/nodes/name.py",
        ]
    )

    assert output.returncode == 0


def test_check_version() -> None:
    """Test that python_ta --version outputs python_ta.__version__ to stdout."""
    stdout = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--version",
        ],
        capture_output=True,
        text=True,
    ).stdout
    assert stdout.rstrip("\n") == python_ta.__version__
