"""Python Teaching Assistant

The goal of this module is to provide automated feedback to students in our
introductory Python courses, using static analysis of their code.

To run the checker, call the check function on the name of the module to check.

> import python_ta
> python_ta.check_all('mymodule.py')

Or, put the following code in your Python module:

if __name__ == '__main__':
    import python_ta
    python_ta.check_all()
"""

from __future__ import annotations

__version__ = "2.10.2.dev"  # Version number
# First, remove underscore from builtins if it has been bound in the REPL.
# Must appear before other imports from pylint/python_ta.
import builtins

try:
    del builtins._
except AttributeError:
    pass


import importlib.util
import logging
import os
import sys
import time
import tokenize
import webbrowser
from builtins import FileNotFoundError
from os import listdir
from typing import IO, Any, AnyStr, Generator, Optional, TextIO, Tuple, Union

import pylint.config
import pylint.lint
import pylint.utils
from astroid import MANAGER, modutils
from pylint.lint import PyLinter
from pylint.reporters import BaseReporter, MultiReporter
from pylint.utils.pragma_parser import OPTION_PO
from watchdog.events import FileSystemEventHandler
from watchdog.observers import Observer

from .check.helpers import (
    check_file,
    get_file_paths,
    get_valid_files_to_check,
    setup_linter,
    upload_linter_results,
    verify_pre_check,
)
from .config import (
    find_local_config,
    load_config,
    load_messages_config,
    override_config,
)
from .patches import patch_all
from .reporters import REPORTERS
from .reporters.core import PythonTaReporter
from .upload import upload_to_server
from .util.autoformat import run_autoformat

HELP_URL = "http://www.cs.toronto.edu/~david/pyta/checkers/index.html"

# Flag to determine if we've previously patched pylint
PYLINT_PATCHED = False


def check_errors(
    module_name: Union[list[str], str] = "",
    config: Union[dict[str, Any], str] = "",
    output: Optional[Union[str, IO]] = None,
    load_default_config: bool = True,
    autoformat: Optional[bool] = False,
) -> PythonTaReporter:
    """Check a module for errors, printing a report."""
    return _check(
        module_name=module_name,
        level="error",
        local_config=config,
        output=output,
        load_default_config=load_default_config,
        autoformat=autoformat,
    )


def check_all(
    module_name: Union[list[str], str] = "",
    config: Union[dict[str, Any], str] = "",
    output: Optional[Union[str, IO]] = None,
    load_default_config: bool = True,
    autoformat: Optional[bool] = False,
) -> PythonTaReporter:
    """Analyse one or more Python modules for code issues and display the results.

    Args:
        module_name:
            If an empty string (default), the module where this function is called is checked.
            If a non-empty string, it is interpreted as a path to a single Python module or a
            directory containing Python modules. If the latter, all Python modules in the directory
            are checked.
            If a list of strings, each string is interpreted as a path to a module or directory,
            and all modules across all paths are checked.
        config:
            If a string, a path to a configuration file to use.
            If a dictionary, a map of configuration options (each key is the name of an option).
        output:
            If a string, a path to a file to which the PythonTA report is written.
            If a typing.IO object, the report is written to this stream.
            If None, the report is written to standard out or automatically displayed in a
            web browser, depending on which reporter is used.
        load_default_config:
            If True (default), additional configuration passed with the ``config`` option is
            merged with the default PythonTA configuration file.
            If False, the default PythonTA configuration is not used.
        autoformat:
            If True, autoformat all modules using the black formatting tool before analyzing code.

    Returns:
        The ``PythonTaReporter`` object that generated the report.
    """
    return _check(
        module_name=module_name,
        level="all",
        local_config=config,
        output=output,
        load_default_config=load_default_config,
        autoformat=autoformat,
    )


def _check(
    module_name: Union[list[str], str] = "",
    level: str = "all",
    local_config: Union[dict[str, Any], str] = "",
    output: Optional[Union[str, IO]] = None,
    load_default_config: bool = True,
    autoformat: Optional[bool] = False,
) -> PythonTaReporter:
    """Check a module for problems, printing a report.

    The `module_name` can take several inputs:
      - string of a directory, or file to check (`.py` extension optional).
      - list of strings of directories or files -- can have multiple.
      - no argument -- checks the python file containing the function call.
    `level` is used to specify which checks should be made.
    `local_config` is a dict of config options or string (config file name).
    `output` is an absolute or relative path to a file, or a typing.IO object to capture pyta data
    output. If None, stdout is used.
    `load_default_config` is used to specify whether to load the default .pylintrc file that comes
    with PythonTA. It will load it by default.
    `autoformat` is used to specify whether the black formatting tool is run. It is not run by default.
    """
    # Configuring logger
    logging.basicConfig(format="[%(levelname)s] %(message)s", level=logging.INFO)
    linter, current_reporter = setup_linter(local_config, load_default_config, output)
    try:
        # Flag indicating whether at least one file has been checked
        is_any_file_checked = False
        linted_files = set()
        for locations in get_valid_files_to_check(module_name):
            f_paths = []  # Paths to files for data submission
            for file_py in get_file_paths(locations):
                linted_files.add(file_py)
                is_any_file_checked, current_reporter, linter = check_file(
                    linter,
                    file_py,
                    local_config,
                    load_default_config,
                    autoformat,
                    is_any_file_checked,
                    current_reporter,
                    level,
                    f_paths,
                )
                current_reporter.print_messages(level)
            upload_linter_results(linter, current_reporter, f_paths, local_config)
        # Only generate reports (display the webpage) if there were valid files to check
        if is_any_file_checked:
            linter.generate_reports()
            if linter.config.watch:
                _watch_files(
                    linted_files,
                    level,
                    local_config,
                    load_default_config,
                    autoformat,
                    linter,
                    current_reporter,
                )
        return current_reporter
    except Exception as e:
        logging.error(
            "Unexpected error encountered! Please report this to your instructor (and attach the code that caused the error)."
        )
        logging.error('Error message: "{}"'.format(e))
        raise e


def doc(msg_id: str) -> None:
    """Open the PythonTA documentation page for the given error message id.

    Args:
        msg_id: The five-character error code, e.g. ``"E0401"``.
    """
    msg_url = HELP_URL + "#" + msg_id.lower()
    print("Opening {} in a browser.".format(msg_url))
    webbrowser.open(msg_url)


def _watch_files(
    file_paths: set,
    level: str,
    local_config: Union[dict[str, Any], str],
    load_default_config: bool,
    autoformat: Optional[bool],
    linter: PyLinter,
    current_reporter: BaseReporter | MultiReporter,
):
    """Watch a list of files for modifications and trigger a callback when changes occur."""

    class FileChangeHandler(FileSystemEventHandler):
        """Internal class to handle file modifications."""

        def __init__(self, files_to_watch):
            self.files_to_watch = set(files_to_watch)
            self.linter = linter
            self.current_reporter = current_reporter

        def on_modified(self, event):
            """Trigger the callback when a watched file is modified."""
            if event.src_path in self.files_to_watch:
                print(f"File modified: {event.src_path}, re-running checks...")

                if event.src_path in self.current_reporter.messages:
                    del self.current_reporter.messages[event.src_path]

                _, self.current_reporter, self.linter = check_file(
                    self.linter,
                    event.src_path,
                    local_config,
                    load_default_config,
                    autoformat,
                    True,
                    self.current_reporter,
                    level,
                    [],
                )
                self.current_reporter.print_messages(level)
                self.linter.generate_reports()
                upload_linter_results(linter, current_reporter, [event.src_path], local_config)

    directories_to_watch = {os.path.dirname(file) for file in file_paths}
    event_handler = FileChangeHandler(file_paths)
    observer = Observer()
    for directory in directories_to_watch:
        observer.schedule(event_handler, path=directory, recursive=False)
    observer.start()

    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        observer.stop()

    observer.join()
