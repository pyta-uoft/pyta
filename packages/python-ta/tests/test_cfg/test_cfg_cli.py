"""
Test suite for the CFG CLI interface.
"""

from unittest.mock import patch

from click.testing import CliRunner

from python_ta.cfg.__main__ import main


class TestCFGCLI:
    """Test the command-line interface for CFG generation."""

    def setup_method(self):
        """Set up the Click test runner."""
        self.runner = CliRunner()

    @patch("python_ta.cfg.__main__.generate_cfg")
    def test_basic_call(self, mock_generate_cfg):
        """Test basic CLI call with just filepath."""
        result = self.runner.invoke(main, ["mock_file.py"])

        assert result.exit_code == 0
        mock_generate_cfg.assert_called_once_with(
            mod="mock_file.py", auto_open=False, visitor_options=None
        )

    @patch("python_ta.cfg.__main__.generate_cfg")
    def test_with_auto_open(self, mock_generate_cfg):
        """Test CLI with --auto-open flag."""
        result = self.runner.invoke(main, ["mock_file.py", "--auto-open"])

        assert result.exit_code == 0
        mock_generate_cfg.assert_called_once_with(
            mod="mock_file.py", auto_open=True, visitor_options=None
        )

    @patch("python_ta.cfg.__main__.generate_cfg")
    def test_with_visitor_options_separate_conditions(self, mock_generate_cfg):
        """Test CLI with visitor options for separate-condition-blocks."""
        options = {"separate-condition-blocks": True}
        result = self.runner.invoke(
            main, ["mock_file.py", "--visitor-options", "separate-condition-blocks=true"]
        )

        assert result.exit_code == 0
        mock_generate_cfg.assert_called_once_with(
            mod="mock_file.py", auto_open=False, visitor_options=options
        )

    @patch("python_ta.cfg.__main__.generate_cfg")
    def test_with_visitor_options_functions(self, mock_generate_cfg):
        """Test CLI with visitor options for specific functions."""
        options = {"functions": ["MyClass.method", "top_level_func"]}
        result = self.runner.invoke(
            main, ["mock_file.py", "--visitor-options", "functions='MyClass.method,top_level_func'"]
        )

        assert result.exit_code == 0
        mock_generate_cfg.assert_called_once_with(
            mod="mock_file.py", auto_open=False, visitor_options=options
        )

    @patch("python_ta.cfg.__main__.generate_cfg")
    def test_with_all_options(self, mock_generate_cfg):
        """Test CLI with all options combined."""
        options = {
            "separate-condition-blocks": True,
            "functions": ["analyze_data", "MyClass.process"],
        }
        result = self.runner.invoke(
            main,
            [
                "mock_file.py",
                "--auto-open",
                "--visitor-options",
                "separate-condition-blocks=true,functions='analyze_data,MyClass.process'",
            ],
        )

        assert result.exit_code == 0
        mock_generate_cfg.assert_called_once_with(
            mod="mock_file.py", auto_open=True, visitor_options=options
        )

    def test_missing_filepath_argument(self):
        """Test CLI without required filepath argument."""
        result = self.runner.invoke(main, [])

        assert result.exit_code == 2
        assert "Missing argument" in result.output

    def test_help_message(self):
        """Test that --help displays expected information."""
        result = self.runner.invoke(main, ["--help"])

        assert result.exit_code == 0
        assert "Generate a Control Flow Graph" in result.output
        assert "--auto-open" in result.output
        assert "--visitor-options" in result.output
        assert "Comma-separated key=value pairs" in result.output
