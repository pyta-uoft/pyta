"""Run from the `pyta` root directory to use the local `python_ta` rather than
installed `python_ta` package.
"""

from os import path

from click.testing import CliRunner

import python_ta
from python_ta.__main__ import main
from python_ta.config import DEFAULT_CONFIG_LOCATION

SOURCE_ROOT = path.normpath(path.join(path.dirname(__file__), "../../.."))
TEST_ROOT = path.join(SOURCE_ROOT, "packages", "python-ta", "tests")
TEST_CONFIG = path.join(TEST_ROOT, "test.pylintrc")


def test_check_no_errors_zero() -> None:
    """Test that python_ta exits with status code 0 when it does not detect errors."""
    runner = CliRunner()
    output = runner.invoke(
        main,
        [  # type: ignore
            "--config",
            TEST_CONFIG,
            path.join(TEST_ROOT, "fixtures", "no_errors.py"),
        ],
    )

    assert output.exit_code == 0


def test_check_errors_nonzero() -> None:
    """Test that python_ta exits with non-zero status code when it detects errors."""
    runner = CliRunner()
    output = runner.invoke(
        main,
        [  # type: ignore
            "--config",
            TEST_CONFIG,
            path.join(SOURCE_ROOT, "examples", "nodes", "name.py"),
        ],
    )

    assert output.exit_code != 0


def test_check_exit_zero() -> None:
    """Test that python_ta --exit-zero always exits with status code 0,
    even when given a file with errors.
    """
    runner = CliRunner()
    output = runner.invoke(
        main,
        [  # type: ignore
            "--exit-zero",
            "--config",
            TEST_CONFIG,
            path.join(SOURCE_ROOT, "examples", "nodes", "name.py"),
        ],
    )

    assert output.exit_code == 0


def test_check_version() -> None:
    """Test that python_ta --version outputs python_ta.__version__ to stdout."""
    runner = CliRunner()
    result = runner.invoke(
        main,
        [  # type: ignore
            "--config",
            TEST_CONFIG,
            "--version",
        ],
    )

    assert result.output.rstrip("\n") == python_ta.__version__


def test_config_generation() -> None:
    """Test that python_ta --generate-config prints the default config to stdout."""
    runner = CliRunner()
    result = runner.invoke(
        main,
        [  # type: ignore
            "--generate-config",
            "--config",
            TEST_CONFIG,
        ],
    )

    pylintrc_location = path.join(
        SOURCE_ROOT,
        "packages",
        "python-ta",
        "src",
        "python_ta",
        DEFAULT_CONFIG_LOCATION,
    )
    with open(pylintrc_location, "r") as f:
        actual_config = f.read()

    generated_config = result.output[:-1]  # Remove trailing newline

    assert generated_config == actual_config


def test_no_config() -> None:
    """Test that python_ta exits with status code 0 when it does not detect errors
    and no config is specified.
    """
    runner = CliRunner()
    output = runner.invoke(
        main,
        [  # type: ignore
            "--output-format",
            "pyta-plain",
            path.join(TEST_ROOT, "fixtures", "no_errors.py"),
        ],
    )

    assert output.exit_code == 0
