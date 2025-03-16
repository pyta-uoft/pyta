"""Contains tests for python_ta watch functionality."""

from unittest.mock import MagicMock, patch

from watchdog.events import FileModifiedEvent

from python_ta.check.watch import FileChangeHandler


@patch("python_ta.check.watch.upload_linter_results")
@patch("python_ta.check.watch.check_file")
def test_watch_on_modified(mock_check_file: MagicMock, mock_upload: MagicMock) -> None:
    """Test that Watch Dectection correctly responds to a file modification event.
    It verifies that the 'check_file' function is triggered, the reporter prints messages,
    and the linting results are uploaded as expected.
    """
    mock_linter = MagicMock()
    mock_reporter = MagicMock()

    mock_linter.reporter = mock_reporter
    mock_check_file.return_value = (None, mock_linter)
    handler = FileChangeHandler(
        files_to_watch={"/mock/path/to/file.py"},
        linter=mock_linter,
        current_reporter=mock_reporter,
        local_config={},
        load_default_config=True,
        autoformat=None,
        level="all",
        f_paths=["/mock/path/to/file.py"],
    )

    mock_event = FileModifiedEvent("/mock/path/to/file.py")
    handler.on_modified(mock_event)
    mock_check_file.assert_called_once_with(
        file_py="/mock/path/to/file.py",
        local_config={},
        load_default_config=True,
        autoformat=None,
        is_any_file_checked=True,
        current_reporter=mock_reporter,
        f_paths=[],
    )
    mock_reporter.print_messages.assert_called_once_with("all")
    mock_upload.assert_called_once_with(mock_linter, mock_reporter, ["/mock/path/to/file.py"], {})


@patch("python_ta.check.watch.upload_linter_results")
@patch("python_ta.check.watch.check_file")
def test_on_modified_with_unwatched_file(
    mock_check_file: MagicMock, mock_upload: MagicMock
) -> None:
    """Test that Watch Detection correctly ignores modifications to unwatched files."""
    mock_linter = MagicMock()
    mock_reporter = MagicMock()

    mock_linter.reporter = mock_reporter
    mock_check_file.return_value = (None, mock_linter)

    handler = FileChangeHandler(
        files_to_watch={"/mock/path/to/file.py"},
        linter=mock_linter,
        current_reporter=mock_reporter,
        local_config={},
        load_default_config=True,
        autoformat=None,
        level="all",
        f_paths=["/mock/path/to/file.py"],
    )

    mock_event = FileModifiedEvent("/mock/path/to/other_file.py")
    handler.on_modified(mock_event)
    mock_check_file.assert_not_called()
    mock_reporter.print_messages.assert_not_called()
    mock_upload.assert_not_called()
