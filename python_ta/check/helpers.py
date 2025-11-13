"""Helper functions for PythonTA's checking and reporting processes.
These functions are designed to support the main checking workflow by
modularizing core operations like file validation, linting, and result uploads.
"""

import importlib.util
import logging
import os
import re
import sys
import tokenize
from configparser import Error as ConfigParserError
from typing import IO, Any, AnyStr, Generator, Literal, Optional, Union

from astroid import MANAGER, modutils
from pylint.config.config_file_parser import _RawConfParser
from pylint.exceptions import UnknownMessageError
from pylint.lint import PyLinter
from pylint.lint.pylinter import _load_reporter_by_class
from pylint.reporters import BaseReporter, MultiReporter
from pylint.utils.pragma_parser import OPTION_PO

from python_ta import __version__

from ..config import (
    find_local_config,
    load_config,
    load_messages_config,
    override_config,
)
from ..patches import patch_all
from ..upload import upload_to_server
from ..util.autoformat import run_autoformat

# Flag to determine if we've previously patched pylint
PYLINT_PATCHED = False


class PytaPyLinter(PyLinter):
    """Extension to PyLinter that blocks the default behavior of loading the output format"""

    def _load_reporters(self, reporter_names: str) -> None:
        """Override to skip the default behaviour"""
        return


def setup_linter(
    local_config: Union[dict[str, Any], str],
    load_default_config: bool,
    output: Optional[Union[str, IO]],
) -> tuple[PyLinter, Union[BaseReporter, MultiReporter]]:
    """Set up the linter and reporter for the check."""
    linter = reset_linter(config=local_config, load_default_config=load_default_config)
    current_reporter = linter.reporter
    current_reporter.set_output(output)
    messages_config_path = linter.config.messages_config_path

    global PYLINT_PATCHED
    if not PYLINT_PATCHED:
        patch_all()
        PYLINT_PATCHED = True
    return linter, current_reporter


def check_file(
    file_py: AnyStr,
    local_config: Union[dict[str, Any], str],
    load_default_config: bool,
    autoformat: Optional[bool],
    is_any_file_checked: bool,
    current_reporter: Union[BaseReporter, MultiReporter],
    f_paths: list,
) -> tuple[bool, PyLinter]:
    """Perform linting on a single Python file using the provided linter and configuration"""
    # Load config file in user location. Construct new linter each
    # time, so config options don't bleed to unintended files.
    # Reuse the same reporter each time to accumulate the results across different files.
    linter = reset_linter(
        config=local_config,
        file_linted=file_py,
        load_default_config=load_default_config,
    )

    if autoformat:
        run_autoformat(file_py, linter.config.autoformat_options, linter.config.max_line_length)

    if not is_any_file_checked:
        prev_output = current_reporter.out
        prev_should_close_out = current_reporter.should_close_out
        current_reporter = linter.reporter
        current_reporter.out = prev_output
        current_reporter.should_close_out = not linter.config.watch and prev_should_close_out

        # At this point, the only possible errors are those from parsing the config file
        # so print them, if there are any.
        if current_reporter.has_messages():
            current_reporter.print_messages()
    else:
        linter.set_reporter(current_reporter)

    # The current file was checked so update the flag
    is_any_file_checked = True

    module_name = os.path.splitext(os.path.basename(file_py))[0]
    if module_name in MANAGER.astroid_cache:  # Remove module from astroid cache
        del MANAGER.astroid_cache[module_name]
    linter.check([file_py])  # Lint !
    if linter.config.pyta_file_permission:
        f_paths.append(file_py)  # Appending paths for upload
    logging.debug(
        "File: {} was checked using the configuration file: {}".format(file_py, linter.config_file)
    )
    logging.debug(
        "File: {} was checked using the messages-config file: {}".format(
            file_py, linter.config.messages_config_path
        )
    )
    return is_any_file_checked, linter


def upload_linter_results(
    linter: PyLinter,
    current_reporter: Union[BaseReporter, MultiReporter],
    f_paths: list,
    local_config: Union[dict[str, Any], str],
) -> None:
    """Upload linter results and configuration data to the specified server if permissions allow."""
    config = {}  # Configuration settings for data submission
    errs = []  # Errors caught in files for data submission
    if linter.config.pyta_error_permission:
        errs = list(current_reporter.messages.values())
    if f_paths != [] or errs != []:  # Only call upload_to_server() if there's something to upload
        # Checks if default configuration was used without changing options through the local_config argument
        if linter.config_file[-19:-10] != "python_ta" or local_config != "":
            config = linter.config.__dict__
        upload_to_server(
            errors=errs,
            paths=f_paths,
            config=config,
            url=linter.config.pyta_server_address,
            version=__version__,
        )


def reset_linter(
    config: Optional[Union[dict, str]] = None,
    file_linted: Optional[AnyStr] = None,
    load_default_config: bool = True,
) -> PyLinter:
    """Construct a new linter. Register config and checker plugins.

    To determine which configuration to use:
    - If the option is enabled, load the default PythonTA config file,
    - If the config argument is a string, use the config found at that location,
    - Otherwise,
        - Try to use the config file at directory of the file being linted,
        - If the config argument is a dictionary, apply those options afterward.
    Do not re-use a linter object. Returns a new linter.
    """

    # Tuple of custom options. Note: 'type' must map to a value equal a key in the pylint/config/option.py `VALIDATORS` dict.
    new_checker_options = (
        (
            "server-port",
            {
                "default": 0,
                "type": "int",
                "metavar": "<port>",
                "help": "Port number for the HTML report server",
            },
        ),
        (
            "watch",
            {
                "default": False,
                "type": "yn",
                "metavar": "<yn>",
                "help": "Run the HTML report server in persistent mode",
            },
        ),
        (
            "pyta-number-of-messages",
            {
                "default": 0,  # If the value is 0, all messages are displayed.
                "type": "int",
                "metavar": "<number_messages>",
                "help": "The maximum number of occurrences of each check to report.",
            },
        ),
        (
            "pyta-template-file",
            {
                "default": "",
                "type": "string",
                "metavar": "<pyta_reporter>",
                "help": "HTML template file for the HTMLReporter.",
            },
        ),
        (
            "pyta-error-permission",
            {
                "default": False,
                "type": "yn",
                "metavar": "<yn>",
                "help": "Permission to anonymously submit errors",
            },
        ),
        (
            "pyta-file-permission",
            {
                "default": False,
                "type": "yn",
                "metavar": "<yn>",
                "help": "Permission to anonymously submit files and errors",
            },
        ),
        (
            "pyta-server-address",
            {
                "default": "http://127.0.0.1:5000",
                "type": "string",
                "metavar": "<server-url>",
                "help": "Server address to submit anonymous data",
            },
        ),
        (
            "messages-config-path",
            {
                "default": os.path.join(
                    os.path.dirname(os.path.dirname(__file__)), "config", "messages_config.toml"
                ),
                "type": "string",
                "metavar": "<messages_config>",
                "help": "Path to patch config toml file.",
            },
        ),
        (
            "allow-pylint-comments",
            {
                "default": False,
                "type": "yn",
                "metavar": "<yn>",
                "help": "Allows or disallows 'pylint:' comments",
            },
        ),
        (
            "use-pyta-error-messages",
            {
                "default": True,
                "type": "yn",
                "metavar": "<yn>",
                "help": "Overwrite the default pylint error messages with PythonTA's messages",
            },
        ),
        (
            "autoformat-options",
            {
                "default": ["skip-string-normalization"],
                "type": "csv",
                "metavar": "<autoformatter options>",
                "help": "List of command-line arguments for black",
            },
        ),
    )

    parent_dir_path = os.path.dirname(os.path.dirname(__file__))
    custom_checkers = [
        ("python_ta.checkers." + os.path.splitext(f)[0])
        for f in os.listdir(os.path.join(parent_dir_path, "checkers"))
        if f != "__init__.py" and os.path.splitext(f)[1] == ".py"
    ]

    # Register new options to a checker here to allow references to
    # options in `.pylintrc` config file.
    # Options stored in linter: `linter._all_options`, `linter._external_opts`
    linter = PytaPyLinter(options=new_checker_options)
    linter.load_default_plugins()  # Load checkers, reporters
    linter.load_plugin_modules(custom_checkers)
    linter.load_plugin_modules(["python_ta.transforms.setendings"])

    default_config_path = find_local_config(os.path.dirname(os.path.dirname(__file__)))
    set_config = load_config

    output_format_override = _get_output_format_override(config)

    reporter_class_path = _get_reporter_class_path(output_format_override)
    reporter_class = _load_reporter_by_class(reporter_class_path)
    linter.set_reporter(reporter_class())

    if load_default_config:
        load_config(linter, default_config_path)
        # If we do specify to load the default config, we just need to override the options later.
        set_config = override_config

    if isinstance(config, str) and config != "":
        set_config(linter, config)
    else:
        # If available, use config file at directory of the file being linted.
        pylintrc_location = None
        if file_linted:
            pylintrc_location = find_local_config(file_linted)

        # Load or override the options if there is a config file in the current directory.
        if pylintrc_location:
            set_config(linter, pylintrc_location)

        # Override part of the default config, with a dict of config options.
        # Note: these configs are overridden by config file in user's codebase
        # location.
        if isinstance(config, dict):
            for key in config:
                linter.set_option(key, config[key])

    # Override error messages
    messages_config_path = linter.config.messages_config_path
    messages_config_default_path = linter._option_dicts["messages-config-path"]["default"]
    use_pyta_error_messages = linter.config.use_pyta_error_messages
    messages_config = load_messages_config(
        messages_config_path, messages_config_default_path, use_pyta_error_messages
    )
    for error_id, new_msg in messages_config.items():
        # Create new message definition object according to configured error messages
        try:
            message = linter.msgs_store.get_message_definitions(error_id)
        except UnknownMessageError:
            logging.warning(f"{error_id} is not a valid error id.")
            continue

        for message_definition in message:
            message_definition.msg = new_msg
            # Mutate the message definitions of the linter object
            linter.msgs_store.register_message(message_definition)

    return linter


def get_valid_files_to_check(module_name: Union[list[str], str]) -> Generator[AnyStr, None, None]:
    """A generator for all valid files to check."""
    # Allow call to check with empty args
    if module_name == "":
        m = sys.modules["__main__"]
        spec = importlib.util.spec_from_file_location(m.__name__, m.__file__)
        module_name = [spec.origin]
    # Enforce API to expect 1 file or directory if type is list
    elif isinstance(module_name, str):
        module_name = [module_name]
    # Otherwise, enforce API to expect `module_name` type as list
    elif not isinstance(module_name, list):
        logging.error(
            "No checks run. Input to check, `{}`, has invalid type, must be a list of strings.".format(
                module_name
            )
        )
        return

    # Filter valid files to check
    for item in module_name:
        if not isinstance(item, str):  # Issue errors for invalid types
            logging.error(
                "No check run on file `{}`, with invalid type. Must be type: str.\n".format(item)
            )
        elif os.path.isdir(item):
            yield item
        elif not os.path.exists(os.path.expanduser(item)):
            try:
                # For files with dot notation, e.g., `examples.<filename>`
                yield modutils.file_from_modpath(item.split("."))
            except ImportError:
                logging.error("Could not find the file called, `{}`\n".format(item))
        else:
            yield item  # Check other valid files.


def get_file_paths(rel_path: AnyStr) -> Generator[AnyStr, None, None]:
    """A generator for iterating python files within a directory.
    `rel_path` is a relative path to a file or directory.
    Returns paths to all files in a directory.
    """
    if not os.path.isdir(rel_path):
        yield rel_path  # Don't do anything; return the file name.
    else:
        for root, _, files in os.walk(rel_path):
            for filename in (f for f in files if f.endswith(".py")):
                yield os.path.join(root, filename)  # Format path, from root.


def verify_pre_check(
    filepath: AnyStr,
    allow_pylint_comments: bool,
    on_verify_fail: Literal["log", "raise"] = "log",
) -> bool:
    """Check student code for certain issues.

    Precondition: `filepath` variable must be a valid file path.

    - `filepath` corresponds to the file path of the file that needs to be checked.
    - `allow_pylint_comments` parameter indicates whether we want the user to be able to add comments
       beginning with pylint which can be used to locally disable checks.
    - `on_verify_fail` determines how to handle files that cannot be checked. In the event that a file cannot be
       checked, if `on_verify_fail="raise"`, then an error is raised. However, if 'on_verify_fail="log"' (default), then
       False is returned.
    """
    # Make sure the program doesn't crash for students.
    # Could use some improvement for better logging and error reporting.
    try:
        # Check for inline "pylint:" comment, which may indicate a student
        # trying to disable a check.
        if allow_pylint_comments:
            return True
        with tokenize.open(os.path.expanduser(filepath)) as f:
            for tok_type, content, _, _, _ in tokenize.generate_tokens(f.readline):
                if tok_type != tokenize.COMMENT:
                    continue
                match = OPTION_PO.search(content)
                if match is not None:
                    logging.error(
                        'String "pylint:" found in comment. '
                        + "No check run on file `{}.`\n".format(filepath)
                    )
                    return False
    except IndentationError as e:
        logging.error(
            "python_ta could not check your code due to an "
            + "indentation error at line {}.".format(e.lineno)
        )
        if on_verify_fail == "raise":
            raise
        return False
    except tokenize.TokenError as e:
        logging.error(
            "python_ta could not check your code due to a " + "syntax error in your file."
        )
        if on_verify_fail == "raise":
            raise
        return False
    except UnicodeDecodeError as e:
        logging.error(
            "python_ta could not check your code due to an "
            + "invalid character. Please check the following lines "
            "in your file and all characters that are marked with a �."
        )
        with open(os.path.expanduser(filepath), encoding="utf-8", errors="replace") as f:
            for i, line in enumerate(f):
                if "�" in line:
                    logging.error(f"  Line {i + 1}: {line}")
        if on_verify_fail == "raise":
            raise
        return False
    return True


def _get_output_format_override(config: Optional[Union[str, dict]]) -> Optional[str]:
    """Retrieve the output format override from the parsed configuration prematurely"""
    output_format_override = None
    if isinstance(config, str) and config != "":
        config_path = os.path.abspath(config)
        if not os.path.exists(config_path):
            logging.warn(f"The following config file was not found: {config}")
            return

        try:
            config_data, _ = _RawConfParser.parse_config_file(config_path, verbose=False)
            output_format_override = config_data.get("output-format")
        except ConfigParserError:
            logging.warn(f"Failed to parse config file {config}")
    elif isinstance(config, dict) and config.get("output-format"):
        output_format_override = config.get("output-format")
    return output_format_override


def _get_reporter_class_path(reporter_name: Optional[str]) -> str:
    """Return the fully qualified class path for a given PyTA reporter name. Defaults to pyta-html"""
    reporter_map = {
        "pyta-html": "python_ta.reporters.html_reporter.HTMLReporter",
        "pyta-plain": "python_ta.reporters.plain_reporter.PlainReporter",
        "pyta-color": "python_ta.reporters.color_reporter.ColorReporter",
        "pyta-json": "python_ta.reporters.json_reporter.JSONReporter",
    }
    return reporter_map.get(reporter_name, "python_ta.reporters.html_reporter.HTMLReporter")
