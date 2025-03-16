"""Module to watch files for modifications and trigger PythonTA checks automatically.
"""

import logging
import os
import time
from typing import Any, Optional, Union

from pylint.lint import PyLinter
from pylint.reporters import BaseReporter, MultiReporter
from watchdog.events import FileSystemEventHandler
from watchdog.observers import Observer

from .helpers import check_file, upload_linter_results


class FileChangeHandler(FileSystemEventHandler):
    """Internal class to handle file modifications."""

    def __init__(
        self,
        files_to_watch: set,
        linter: PyLinter,
        current_reporter: Union[BaseReporter, MultiReporter],
        local_config: Union[dict[str, Any], str],
        load_default_config: bool,
        autoformat: Optional[bool],
        level: str,
        f_paths: list[str],
    ) -> None:
        self.files_to_watch = set(files_to_watch)
        self.linter = linter
        self.current_reporter = current_reporter
        self.local_config = local_config
        self.load_default_config = load_default_config
        self.autoformat = autoformat
        self.level = level
        self.f_paths = f_paths

    def on_modified(self, event) -> None:
        """Trigger the callback when a watched file is modified."""
        if event.src_path not in self.files_to_watch:
            return

        logging.info(f"File modified: {event.src_path}, re-running checks...")
        if event.src_path in self.current_reporter.messages:
            del self.current_reporter.messages[event.src_path]

        _, self.linter = check_file(
            file_py=event.src_path,
            local_config=self.local_config,
            load_default_config=self.load_default_config,
            autoformat=self.autoformat,
            is_any_file_checked=True,
            current_reporter=self.current_reporter,
            f_paths=[],
        )
        self.current_reporter = self.linter.reporter
        self.current_reporter.print_messages(self.level)
        self.linter.generate_reports()
        upload_linter_results(self.linter, self.current_reporter, self.f_paths, self.local_config)

    def on_close(self) -> None:
        """Closes the current reporter's output stream"""
        self.current_reporter.on_close(self.linter.stats, None)


def watch_files(
    file_paths: set,
    level: str,
    local_config: Union[dict[str, Any], str],
    load_default_config: bool,
    autoformat: Optional[bool],
    linter: PyLinter,
    current_reporter: Union[BaseReporter, MultiReporter],
    f_paths: list[str],
) -> None:
    """Watch a list of files for modifications and trigger a callback when changes occur."""
    logging.info("PythonTA is monitoring your files for changes and will re-check after every save")
    directories_to_watch = {os.path.dirname(file) for file in file_paths}
    event_handler = FileChangeHandler(
        files_to_watch=file_paths,
        linter=linter,
        current_reporter=current_reporter,
        local_config=local_config,
        load_default_config=load_default_config,
        autoformat=autoformat,
        level=level,
        f_paths=f_paths,
    )
    observer = Observer()
    for directory in directories_to_watch:
        observer.schedule(event_handler, path=directory, recursive=False)
    observer.start()

    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        event_handler.on_close()
        observer.stop()

    observer.join()
