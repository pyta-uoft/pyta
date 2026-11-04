"""
Test suite for the python_ta.debug CLI interface.
"""

from unittest.mock import patch

from click.testing import CliRunner

from python_ta.debug.__main__ import main


class TestDebugCLI:
    """Test the command-line interface for the debug module."""

    def setup_method(self):
        """Set up the Click test runner."""
        self.runner = CliRunner()

    @patch("python_ta.debug.__main__.run_with_snapshots")
    def test_snapshot_calls_run_with_snapshots(self, mock_run_with_snapshots, tmp_path):
        """Test that the snapshot subcommand runs the given file with snapshot comments enabled."""
        path = tmp_path / "demo.py"
        path.touch()

        result = self.runner.invoke(main, ["snapshot", str(path)])

        assert result.exit_code == 0
        mock_run_with_snapshots.assert_called_once_with(str(path))

    @patch("python_ta.debug.__main__.run_with_snapshots")
    def test_snapshot_missing_file(self, mock_run_with_snapshots, tmp_path):
        """Test that the snapshot subcommand exits with an error when the file does not exist."""
        result = self.runner.invoke(main, ["snapshot", str(tmp_path / "missing.py")])

        assert result.exit_code == 2
        mock_run_with_snapshots.assert_not_called()
