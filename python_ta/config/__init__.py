"""
Within the config submodule, this .py file encompasses functions responsible
 for managing all configuration-related tasks.
"""

import logging
import os
import sys
from pathlib import Path
from typing import AnyStr, Optional

import toml
from pylint.config.config_file_parser import _ConfigurationFileParser
from pylint.config.config_initialization import _config_initialization
from pylint.config.exceptions import _UnrecognizedOptionError
from pylint.lint import PyLinter

DEFAULT_CONFIG_LOCATION = os.path.join("config", ".pylintrc")


def find_local_config(curr_dir: AnyStr) -> Optional[AnyStr]:
    """Search for a `.pylintrc` configuration file provided in same (user)
    location as the source file to check.
    Return absolute path to the file, or None.
    `curr_dir` is an absolute path to a directory, containing a file to check.
    For more info see, pylint.config.find_pylintrc
    """
    if curr_dir.endswith(".py"):
        curr_dir = os.path.dirname(curr_dir)
    if os.path.exists(os.path.join(curr_dir, "config", ".pylintrc")):
        return os.path.join(curr_dir, "config", ".pylintrc")
    elif os.path.exists(os.path.join(curr_dir, "config", "pylintrc")):
        return os.path.join(curr_dir, "config", "pylintrc")


def load_config(linter: PyLinter, config_location: AnyStr) -> None:
    """Load configuration into the linter."""
    _config_initialization(linter, args_list=[], config_file=config_location)
    linter.config_file = config_location


def override_config(linter: PyLinter, config_location: AnyStr) -> None:
    """Override the default linter configuration options (if possible).

    Snippets taken from pylint.config.config_initialization.
    """
    linter.set_current_module(config_location)

    # Read the configuration file.
    config_file_parser = _ConfigurationFileParser(verbose=True, linter=linter)
    try:
        _, config_args = config_file_parser.parse_config_file(file_path=config_location)
    except OSError as ex:
        logging.error(ex)
        sys.exit(32)

    # Override the config options by parsing the provided file.
    try:
        linter._parse_configuration_file(config_args)
    except _UnrecognizedOptionError as exc:
        unrecognized_options_message = ", ".join(exc.options)
        linter.add_message("unrecognized-option", args=unrecognized_options_message, line=0)

    # Everything has been set up already so emit any stashed messages.
    linter._emit_stashed_messages()

    linter.config_file = config_location


def load_messages_config(path: str, default_path: str, use_pyta_error_messages: bool) -> dict:
    """Given path (potentially) specified by user and default default_path
    of messages config file, merge the config files. We will only add the
    PythonTA error messages if use_pyta_error_messages is True.
    """
    # assume the user is not going to provide a path which is the same as the default
    if Path(default_path).resolve() == Path(path).resolve():
        merge_from = {}
    else:
        try:
            merge_from = toml.load(path)
        except FileNotFoundError:
            logging.warning(f"Could not find messages config file at {str(Path(path).resolve())}.")
            merge_from = {}

    # The TOML file has section headers, parse it to get rid of section headers
    if merge_from != {} and "pylint" in list(merge_from.keys())[0]:
        merge_from = _parse_config_with_section_headers(merge_from)

    if not use_pyta_error_messages:
        return merge_from

    # Merge default pyta error messages into custom error messages
    merge_into = _parse_config_with_section_headers(toml.load(default_path))
    merge_into.update(merge_from)
    return merge_into


def _parse_config_with_section_headers(config_dict: dict) -> dict:
    """Given the dictionary representation of a message configuration file with section headers,
    parse it such that all section headers are ignored.
    """
    final_dict = {}
    for category in config_dict:
        for checker in config_dict[category]:
            for error_code in config_dict[category][checker]:
                final_dict[error_code] = config_dict[category][checker][error_code]
    return final_dict
