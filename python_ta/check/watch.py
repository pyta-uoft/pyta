"""Module to watch files for modifications and trigger PythonTA checks automatically."""

import logging
import os
import time
from typing import Any, Optional, Union

from pylint.lint import PyLinter
from watchdog.events import FileSystemEventHandler
from watchdog.observers import Observer

from .helpers import check_file, upload_linter_results


class FileChangeHandler(FileSystemEventHandler):
    """Internal class to handle file modifications."""

    def __init__(
        self,
        files_to_watch: set,
        linter: PyLinter,
        local_config: Union[dict[str, Any], str],
        load_default_config: bool,
        autoformat: Optional[bool],
        level: str,
        f_paths: list[str],
    ) -> None:
        self.files_to_watch = set(files_to_watch)
        self.linter = linter
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

        current_reporter = self.linter.reporter
        if event.src_path in current_reporter.messages:
            del current_reporter.messages[event.src_path]

        _, self.linter = check_file(
            file_py=event.src_path,
            local_config=self.local_config,
            load_default_config=self.load_default_config,
            autoformat=self.autoformat,
            is_any_file_checked=True,
            current_reporter=current_reporter,
            f_paths=[],
        )
        current_reporter = self.linter.reporter
        current_reporter.print_messages(self.level)
        self.linter.generate_reports()
        upload_linter_results(self.linter, current_reporter, self.f_paths, self.local_config)


def watch_files(
    file_paths: set,
    level: str,
    local_config: Union[dict[str, Any], str],
    load_default_config: bool,
    autoformat: Optional[bool],
    linter: PyLinter,
    f_paths: list[str],
) -> None:
    """Watch a list of files for modifications and trigger a callback when changes occur."""
    directories_to_watch = {os.path.dirname(file) for file in file_paths}
    event_handler = FileChangeHandler(
        files_to_watch=file_paths,
        linter=linter,
        local_config=local_config,
        load_default_config=load_default_config,
        autoformat=autoformat,
        level=level,
        f_paths=f_paths,
    )
    observer = Observer()
    for directory in directories_to_watch:
        observer.schedule(event_handler, path=directory, recursive=False)
    logging.info("PythonTA is monitoring your files for changes and will re-check after every save")
    observer.start()

    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        event_handler.linter.reporter.should_close_out = True
        event_handler.linter.reporter.on_close(event_handler.linter.stats, None)
        observer.stop()

    observer.join()
