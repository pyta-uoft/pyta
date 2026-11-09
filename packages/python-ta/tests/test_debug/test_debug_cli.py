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
        mock_run_with_snapshots.assert_called_once_with(str(path), save=True)

    @patch("python_ta.debug.__main__.run_with_snapshots")
    def test_snapshot_missing_file(self, mock_run_with_snapshots, tmp_path):
        """Test that the snapshot subcommand exits with an error when the file does not exist."""
        result = self.runner.invoke(main, ["snapshot", str(tmp_path / "missing.py")])

        assert result.exit_code == 2
        mock_run_with_snapshots.assert_not_called()

    @patch("python_ta.debug.__main__.run_with_snapshots")
    def test_snapshot_no_save(self, mock_run_with_snapshots, tmp_path):
        """Test that --no-save passes save=False to run_with_snapshots."""
        path = tmp_path / "demo.py"
        path.touch()

        result = self.runner.invoke(main, ["snapshot", str(path), "--no-save"])

        assert result.exit_code == 0
        mock_run_with_snapshots.assert_called_once_with(str(path), save=False)

    @patch("python_ta.debug.__main__.run_with_snapshots")
    def test_snapshot_save(self, mock_run_with_snapshots, tmp_path):
        """Test that --save passes save=True to run_with_snapshots."""
        path = tmp_path / "demo.py"
        path.touch()

        result = self.runner.invoke(main, ["snapshot", str(path), "--save"])

        assert result.exit_code == 0
        mock_run_with_snapshots.assert_called_once_with(str(path), save=True)

    @patch("python_ta.debug.__main__.run_with_snapshots")
    def test_snapshot_memory_viz_args(self, mock_run_with_snapshots, tmp_path):
        """Test that --memory-viz-args is split into a list of MemoryViz CLI arguments."""
        path = tmp_path / "demo.py"
        path.touch()

        result = self.runner.invoke(
            main,
            [
                "snapshot",
                str(path),
                "--memory-viz-args",
                "--width 1000 --roughjs-config seed=12345 --output 'my dir/demo.svg'",
            ],
        )

        assert result.exit_code == 0
        mock_run_with_snapshots.assert_called_once_with(
            str(path),
            save=True,
            memory_viz_args=[
                "--width",
                "1000",
                "--roughjs-config",
                "seed=12345",
                "--output",
                "my dir/demo.svg",
            ],
        )

    @patch("python_ta.debug.__main__.run_with_snapshots")
    def test_snapshot_memory_viz_version(self, mock_run_with_snapshots, tmp_path):
        """Test that --memory-viz-version is passed to run_with_snapshots."""
        path = tmp_path / "demo.py"
        path.touch()

        result = self.runner.invoke(main, ["snapshot", str(path), "--memory-viz-version", "0.3.1"])

        assert result.exit_code == 0
        mock_run_with_snapshots.assert_called_once_with(
            str(path), save=True, memory_viz_version="0.3.1"
        )

    @patch("python_ta.debug.__main__.run_with_snapshots")
    def test_snapshot_frame_and_var_filters(self, mock_run_with_snapshots, tmp_path):
        """Test that repeated --include-frame, --exclude-frame and --exclude-var options are
        passed to run_with_snapshots as lists."""
        path = tmp_path / "demo.py"
        path.touch()

        result = self.runner.invoke(
            main,
            [
                "snapshot",
                str(path),
                "--include-frame",
                "func",
                "--include-frame",
                "helper",
                "--exclude-frame",
                "_private",
                "--exclude-var",
                "x",
                "--exclude-var",
                "y",
            ],
        )

        assert result.exit_code == 0
        mock_run_with_snapshots.assert_called_once_with(
            str(path),
            save=True,
            include_frames=["func", "helper"],
            exclude_frames=["_private"],
            exclude_vars=["x", "y"],
        )
