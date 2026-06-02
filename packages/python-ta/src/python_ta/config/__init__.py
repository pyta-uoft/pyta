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
    elif os.path.exists(os.path.join(curr_dir, "config", "pyproject.toml")):
        return os.path.join(curr_dir, "config", "pyproject.toml")


def load_config(linter: PyLinter, config_location: AnyStr) -> None:
    """Load configuration into the linter."""
    args_list = _get_pyta_toml_args(config_location, linter)
    _config_initialization(linter, args_list=args_list, config_file=config_location)
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

    config_args.extend(_get_pyta_toml_args(config_location, linter))

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

    # Flatten the config dictionary to get rid of section headers (if any)
    merge_from = flatten(merge_from)

    if not use_pyta_error_messages:
        return merge_from

    # Merge default pyta error messages into custom error messages
    merge_into = flatten(toml.load(default_path))
    merge_into.update(merge_from)
    return merge_into


def flatten(config_dict: dict) -> dict:
    """Given a nested dictionary, flatten it such that no values are themselves dictionaries."""
    flat_dict = {}
    for key, value in config_dict.items():
        if isinstance(value, dict):
            flat_dict.update(flatten(value))
        else:
            flat_dict[key] = value
    return flat_dict


def _get_pyta_toml_args(config_location: AnyStr, linter: PyLinter) -> list[str]:
    """Extracts [tool.python-ta] options from a TOML file and formats them as arguments."""
    args_list = []
    if not (config_location and config_location.endswith(".toml")):
        return args_list

    try:
        with open(config_location, "r") as f:
            config_data = toml.load(f)
    except OSError as ex:
        logging.error(ex)
        return args_list
    except toml.TomlDecodeError as ex:
        linter.add_message("config-parse-error", line=0, args=str(ex))
        return args_list

    pyta_config = config_data.get("tool", {}).get("python-ta", {})
    merged_pyta_config = flatten(pyta_config)

    for key, value in merged_pyta_config.items():
        if isinstance(value, list):
            args_list.extend([f"--{key}", ",".join(map(str, value))])
        else:
            args_list.extend([f"--{key}", str(value)])

    return args_list
