"""Run from the `pyta` root directory to use the local `python_ta` rather than
installed `python_ta` package.
"""

from collections.abc import Callable
from os import path
from typing import Any

from click.testing import CliRunner
from pylint.reporters import BaseReporter

import python_ta
import python_ta.__main__ as pyta_main
from python_ta.__main__ import main
from python_ta.config import DEFAULT_CONFIG_LOCATION

SOURCE_ROOT = path.normpath(path.join(path.dirname(__file__), "../../.."))
TEST_ROOT = path.join(SOURCE_ROOT, "packages", "python-ta", "tests")
TEST_CONFIG = path.join(TEST_ROOT, "test.pylintrc")


class _DummyReporter(BaseReporter):
    def has_messages(self) -> bool:
        return False


def mock_checker(calls: list[dict[str, Any]]) -> Callable[..., BaseReporter]:
    def fake_checker(*, module_name: list[str], **kwargs: Any) -> BaseReporter:
        calls.append({"module_name": module_name, **kwargs})
        return _DummyReporter()

    return fake_checker


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
    monkeypatch.setattr(pyta_main, "check_all", mock_checker(calls))

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
    monkeypatch.setattr(pyta_main, "check_all", mock_checker(calls))

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
    assert calls[0].get("pylint_args") is None


def test_config_only_passes_config_path(monkeypatch) -> None:
    """Test that checker receives the config path string if only --config is passed."""
    calls = []
    monkeypatch.setattr(pyta_main, "check_all", mock_checker(calls))

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
    assert calls[0].get("pylint_args") is None


def test_no_output_format_or_config_uses_defaults(monkeypatch) -> None:
    """Test that checker is called without config if neither --config nor --output-format is passed."""
    calls = []
    monkeypatch.setattr(pyta_main, "check_all", mock_checker(calls))

    runner = CliRunner()
    result = runner.invoke(
        pyta_main.main,
        [path.join(TEST_ROOT, "fixtures", "no_errors.py")],
    )

    assert result.exit_code == 0
    assert len(calls) == 1
    assert calls[0]["autoformat"] is False


def test_autoformat_passes_true_to_check_all(monkeypatch) -> None:
    """Test that --autoformat enables autoformatting when running all checks."""
    calls = []
    monkeypatch.setattr(pyta_main, "check_all", mock_checker(calls))

    runner = CliRunner()
    result = runner.invoke(
        pyta_main.main,
        [
            "--autoformat",
            path.join(TEST_ROOT, "fixtures", "no_errors.py"),
        ],
    )

    assert result.exit_code == 0
    assert len(calls) == 1
    assert calls[0]["autoformat"] is True


def test_autoformat_passes_true_to_check_errors(monkeypatch) -> None:
    """Test that --autoformat enables autoformatting when running error checks."""
    calls = []
    monkeypatch.setattr(pyta_main, "check_errors", mock_checker(calls))

    runner = CliRunner()
    result = runner.invoke(
        pyta_main.main,
        [
            "--errors-only",
            "--autoformat",
            path.join(TEST_ROOT, "fixtures", "no_errors.py"),
        ],
    )

    assert result.exit_code == 0
    assert len(calls) == 1
    assert calls[0]["autoformat"] is True


def test_stdin_flag_reads_from_stdin(monkeypatch) -> None:
    """Test that --stdin reads source code from stdin and passes it to the checker."""
    calls = []
    monkeypatch.setattr(pyta_main, "check_all", mock_checker(calls))

    runner = CliRunner()
    result = runner.invoke(
        pyta_main.main,
        ["--stdin"],
        input="x = 1\n",
    )

    assert result.exit_code == 0
    assert len(calls) == 1
    # module_name should be a list with one temp file path ending in .py
    assert len(calls[0]["module_name"]) == 1
    assert calls[0]["module_name"][0].endswith(".py")


def test_dash_filename_reads_from_stdin(monkeypatch) -> None:
    """Test that passing - as the filename triggers stdin mode."""
    calls = []
    monkeypatch.setattr(pyta_main, "check_all", mock_checker(calls))

    runner = CliRunner()
    result = runner.invoke(
        pyta_main.main,
        ["-"],
        input="x = 1\n",
    )

    assert result.exit_code == 0
    assert len(calls) == 1
    assert calls[0]["module_name"][0].endswith(".py")


def test_stdin_contents_written_to_temp_file(monkeypatch) -> None:
    """Test that the stdin contents are correctly written to the temp file passed to the checker."""
    source_code = "x = 1\ny = 2\n"
    calls = []
    monkeypatch.setattr(pyta_main, "check_all", mock_checker(calls))

    runner = CliRunner()
    runner.invoke(
        pyta_main.main,
        ["--stdin"],
        input=source_code,
    )

    assert len(calls) == 1
    assert len(calls[0]["module_name"]) == 1


def test_stdin_temp_file_deleted_after_check(monkeypatch) -> None:
    """Test that the temp file created for stdin is deleted after checking."""
    calls = []
    monkeypatch.setattr(pyta_main, "check_all", mock_checker(calls))

    runner = CliRunner()
    runner.invoke(
        pyta_main.main,
        ["--stdin"],
        input="x = 1\n",
    )

    assert len(calls) == 1
    temp_file_path = calls[0]["module_name"][0]
    assert not path.exists(temp_file_path), "Temp file should be deleted after check"
