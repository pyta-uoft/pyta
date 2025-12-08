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

__version__ = "2.12.0"  # Version number
# First, remove underscore from builtins if it has been bound in the REPL.
# Must appear before other imports from pylint/python_ta.
import builtins

try:
    del builtins._
except AttributeError:
    pass


import logging
import webbrowser
from typing import IO, TYPE_CHECKING, Any, Literal, Optional, Union

from .check.helpers import (
    check_file,
    get_file_paths,
    get_valid_files_to_check,
    setup_linter,
    upload_linter_results,
    verify_pre_check,
)
from .check.watch import watch_files

if TYPE_CHECKING:
    from .reporters.core import PythonTaReporter

HELP_URL = "http://www.cs.toronto.edu/~david/pyta/checkers/index.html"


def check_errors(
    module_name: Union[list[str], str] = "",
    config: Union[dict[str, Any], str] = "",
    output: Optional[Union[str, IO]] = None,
    load_default_config: bool = True,
    autoformat: Optional[bool] = False,
    on_verify_fail: Literal["log", "raise"] = "log",
) -> PythonTaReporter:
    """Check a module for errors, printing a report."""
    return _check(
        module_name=module_name,
        level="error",
        local_config=config,
        output=output,
        load_default_config=load_default_config,
        autoformat=autoformat,
        on_verify_fail=on_verify_fail,
    )


def check_all(
    module_name: Union[list[str], str] = "",
    config: Union[dict[str, Any], str] = "",
    output: Optional[Union[str, IO]] = None,
    load_default_config: bool = True,
    autoformat: Optional[bool] = False,
    on_verify_fail: Literal["log", "raise"] = "log",
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
        on_verify_fail:
            Determines how to handle files that cannot be checked. If set to "log" (default), an error
            message is logged and execution continues. If set to "raise", an error is raised immediately to stop
            execution.

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
        on_verify_fail=on_verify_fail,
    )


def _check(
    module_name: Union[list[str], str] = "",
    level: str = "all",
    local_config: Union[dict[str, Any], str] = "",
    output: Optional[Union[str, IO]] = None,
    load_default_config: bool = True,
    autoformat: Optional[bool] = False,
    on_verify_fail: Literal["log", "raise"] = "log",
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
    `on_verify_fail` determines how to handle files that cannot be checked. If set to "log" (default), an error
     message is logged and execution continues. If set to "raise", an error is raised immediately to stop execution.
    """
    # Configuring logger
    logging.basicConfig(format="[%(levelname)s] %(message)s", level=logging.INFO)
    linter, current_reporter = setup_linter(local_config, load_default_config, output)
    try:
        # Flag indicating whether at least one file has been checked
        is_any_file_checked = False
        linted_files = set()
        f_paths = []  # Paths to files for data submission
        for locations in get_valid_files_to_check(module_name):
            f_paths = []
            for file_py in get_file_paths(locations):
                linted_files.add(file_py)
                if not verify_pre_check(
                    file_py, linter.config.allow_pylint_comments, on_verify_fail=on_verify_fail
                ):
                    # The only way to reach this is if verify_pre_check returns False, and `on_verify_fail="log"`.
                    continue
                is_any_file_checked, linter = check_file(
                    file_py=file_py,
                    local_config=local_config,
                    load_default_config=load_default_config,
                    autoformat=autoformat,
                    is_any_file_checked=is_any_file_checked,
                    current_reporter=current_reporter,
                    f_paths=f_paths,
                )
                current_reporter = linter.reporter
                current_reporter.print_messages(level)
            upload_linter_results(linter, current_reporter, f_paths, local_config)
        # Only generate reports (display the webpage) if there were valid files to check
        if is_any_file_checked:
            linter.generate_reports()
            if linter.config.watch:
                watch_files(
                    file_paths=linted_files,
                    level=level,
                    local_config=local_config,
                    load_default_config=load_default_config,
                    autoformat=autoformat,
                    linter=linter,
                    f_paths=f_paths,
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
