"""Run from the `pyta` root directory to use the local `python_ta` rather than
installed `python_ta` package.
"""

import subprocess
import sys
from os import environ, path

import python_ta

# Find the source root directory
source = path.dirname(__file__)
while path.basename(source) != "pyta":
    source = path.dirname(source)

# Gives absolute path to source root directory (pyta)
SOURCE_ROOT = source
# SOURCE_ROOT = path.normpath(path.join(path.dirname(__file__), ".."))  # NOTE: Professor may prefer this approach

# Defines relative path to the default config directory (python_ta/config)
CONFIG_LOCATION = path.join("python_ta", "config")

# Gives absolute path to the default config file ($SOURCE_ROOT/$CONFIG_LOCATION/.pylintrc)
DEFAULT_CONFIG_FILE_PATH = path.join(SOURCE_ROOT, CONFIG_LOCATION, ".pylintrc")

# Gives absolute path to the testing directory ($SOURCE_ROOT/tests)
TEST_DIR = path.join(SOURCE_ROOT, "tests")

# Gives absolute path to the config file used for testing ($TEST_DIR/test.pylintrc)
TEST_CONFIG_FILE_PATH = path.join(TEST_DIR, "test.pylintrc")


def test_check_no_errors_zero() -> None:
    """Test that python_ta exits with status code 0 when it does not detect errors."""
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            TEST_CONFIG_FILE_PATH,
            path.join(TEST_DIR, "fixtures", "no_errors.py"),
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
            TEST_CONFIG_FILE_PATH,
            path.join(SOURCE_ROOT, "examples", "nodes", "name.py"),
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
            TEST_CONFIG_FILE_PATH,
            path.join(SOURCE_ROOT, "examples", "nodes", "name.py"),
        ],
        env={**environ, "PYTHONIOENCODING": "utf-8"},
    )

    assert output.returncode == 0


def test_check_version() -> None:
    """Test that python_ta --version outputs python_ta.__version__ to stdout."""
    stdout = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            TEST_CONFIG_FILE_PATH,
            "--version",
        ],
        capture_output=True,
        text=True,
    ).stdout

    assert stdout.rstrip("\n") == python_ta.__version__


def test_config_generation() -> None:
    """Test that python_ta --generate-config prints the default config to stdout."""
    generated_config = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--generate-config",
            "--config",
            TEST_CONFIG_FILE_PATH,
        ],
        capture_output=True,
        text=True,
    ).stdout

    with open(DEFAULT_CONFIG_FILE_PATH, "r") as f:
        actual_config = f.read()

    generated_config = generated_config[:-1]  # Remove trailing newline

    assert generated_config == actual_config


def test_no_config() -> None:
    """Test that python_ta exits with status code 0 when it does not detect errors
    and no config is specified.
    """
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--output-format",
            "python_ta.reporters.PlainReporter",
            path.join(TEST_DIR, "fixtures", "no_errors.py"),
        ],
    )

    assert output.returncode == 0
