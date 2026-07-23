"""Run from the `pyta` root directory to use the local `python_ta` rather than
installed `python_ta` package.
"""

from os import path

from click.testing import CliRunner

import python_ta
import python_ta.__main__ as pyta_main
from python_ta.__main__ import main
from python_ta.config import DEFAULT_CONFIG_LOCATION

SOURCE_ROOT = path.normpath(path.join(path.dirname(__file__), "../../.."))
TEST_ROOT = path.join(SOURCE_ROOT, "packages", "python-ta", "tests")
TEST_CONFIG = path.join(TEST_ROOT, "test.pylintrc")


class _DummyReporter:
    def has_messages(self) -> bool:
        return False


def test_check_no_errors_zero() -> None:
    """Test that python_ta exits with status code 0 when it does not detect errors."""
    runner = CliRunner()
    output = runner.invoke(
        main,
        [
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
        [
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
        [
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
        [
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
        [
            "--generate-config",
            "--config",
            TEST_CONFIG,
        ],
    )

    config_location = path.join(
        SOURCE_ROOT,
        "packages",
        "python-ta",
        "src",
        "python_ta",
        DEFAULT_CONFIG_LOCATION,
    )
    with open(config_location, "r") as f:
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
        [
            "--output-format",
            "pyta-plain",
            path.join(TEST_ROOT, "fixtures", "no_errors.py"),
        ],
    )

    assert output.exit_code == 0


def test_output_format_overrides_config_value(monkeypatch, tmp_path) -> None:
    """Test that CLI output-format takes precedence if both --config and --output-format are passed."""
    config_file = tmp_path / "pyproject.toml"
    config_file.write_text(
        """
        [tool.python-ta]
        output-format = "pyta-html"
        max-line-length = 90
        """.strip(),
        encoding="utf-8",
    )

    calls = []

    def fake_checker(*, module_name, config=None, pylint_args=None):
        calls.append({"module_name": module_name, "config": config, "pylint_args": pylint_args})
        return _DummyReporter()

    monkeypatch.setattr(pyta_main, "check_all", fake_checker)

    runner = CliRunner()
    result = runner.invoke(
        pyta_main.main,
        [
            "--config",
            str(config_file),
            "--output-format",
            "pyta-plain",
            path.join(TEST_ROOT, "fixtures", "no_errors.py"),
        ],
    )

    assert result.exit_code == 0
    assert len(calls) == 1
    assert calls[0]["config"] == str(config_file)
    assert calls[0]["pylint_args"] == ["--output-format", "pyta-plain"]


def test_output_format_only_passes_output_format_dict(monkeypatch) -> None:
    """Test that checker receives only the override dict if only --output-format is passed."""
    calls = []

    def fake_checker(*, module_name, config=None, pylint_args=None):
        calls.append({"module_name": module_name, "config": config, "pylint_args": pylint_args})
        return _DummyReporter()

    monkeypatch.setattr(pyta_main, "check_all", fake_checker)

    runner = CliRunner()
    result = runner.invoke(
        pyta_main.main,
        [
            "--output-format",
            "pyta-plain",
            path.join(TEST_ROOT, "fixtures", "no_errors.py"),
        ],
    )

    assert result.exit_code == 0
    assert len(calls) == 1
    assert calls[0]["config"] == {"output-format": "pyta-plain"}
    assert calls[0]["pylint_args"] is None


def test_config_only_passes_config_path(monkeypatch) -> None:
    """Test that checker receives the config path string if only --config is passed."""
    calls = []

    def fake_checker(*, module_name, config=None, pylint_args=None):
        calls.append({"module_name": module_name, "config": config, "pylint_args": pylint_args})
        return _DummyReporter()

    monkeypatch.setattr(pyta_main, "check_all", fake_checker)

    runner = CliRunner()
    result = runner.invoke(
        pyta_main.main,
        [
            "--config",
            TEST_CONFIG,
            path.join(TEST_ROOT, "fixtures", "no_errors.py"),
        ],
    )

    assert result.exit_code == 0
    assert len(calls) == 1
    assert calls[0]["config"] == path.abspath(TEST_CONFIG)
    assert calls[0]["pylint_args"] is None


def test_no_output_format_or_config_uses_defaults(monkeypatch) -> None:
    """Test that checker is called without config if neither --config nor --output-format is passed."""
    calls = []

    def fake_checker(*, module_name, **kwargs):
        calls.append({"module_name": module_name, "kwargs": kwargs})
        return _DummyReporter()

    monkeypatch.setattr(pyta_main, "check_all", fake_checker)

    runner = CliRunner()
    result = runner.invoke(
        pyta_main.main,
        [path.join(TEST_ROOT, "fixtures", "no_errors.py")],
    )

    assert result.exit_code == 0
    assert len(calls) == 1
    assert calls[0]["kwargs"] == {}
