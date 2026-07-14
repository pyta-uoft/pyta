from __future__ import annotations

import configparser
import sys
from os import path
from typing import Optional

import click
import toml

from python_ta import __version__, check_all, check_errors
from python_ta.config import DEFAULT_CONFIG_LOCATION, flatten

CONTEXT_SETTINGS = dict(help_option_names=["-h", "--help"])


def _load_config_as_dict(config_path: str) -> dict[str, str]:
    """Load a config file and return it as a dictionary of option: value pairs."""
    if config_path.endswith(".toml"):
        return flatten(toml.load(config_path).get("tool", {}).get("python-ta", {}))
    else:
        parser = configparser.ConfigParser()
        parser.read(config_path)
        return {
            option: value
            for section in parser.sections()
            for option, value in parser.items(section)
        }


@click.command(context_settings=CONTEXT_SETTINGS)
@click.option(
    "-v", "--version", is_flag=True, help="Print current version of PythonTA.", default=False
)
@click.option(
    "-c",
    "--config",
    type=click.Path(exists=True, dir_okay=False, resolve_path=True),
    help="python_ta configuration file",
)
@click.option("-E", "--errors-only", is_flag=True, help="Displays errors only", default=False)
@click.argument(
    "filenames", nargs=-1, type=click.Path(exists=True, dir_okay=True, resolve_path=True)
)
@click.option("--exit-zero", is_flag=True, help="Always return with status code 0", default=False)
@click.option(
    "-g",
    "--generate-config",
    is_flag=True,
    help="Print out default PythonTA configuration file",
    default=False,
)
@click.option(
    "--output-format",
    help="Specify the format of output report. This option overrides the output format specified in the config file.",
    default=None,
)
def main(
    version: bool,
    config: Optional[str],
    errors_only: bool,
    filenames: list[str],
    exit_zero: bool,
    generate_config: bool,
    output_format: Optional[str],
) -> None:
    """A code checking tool for teaching Python.
    FILENAMES can be a string of a directory, or file to check (`.py` extension optional) or
    a list of strings of directories or files.
    """
    if version:
        print(__version__)
        return

    # `config` is None if `-c` flag is not set
    if generate_config:
        config_location = path.join(path.dirname(__file__), DEFAULT_CONFIG_LOCATION)
        with open(config_location, "r") as f:
            contents = f.read()
            print(contents)
            sys.exit(0)

    checker = check_errors if errors_only else check_all
    paths = [click.format_filename(fn) for fn in filenames]

    if output_format and config:
        # If both specified, use the config file and override the output format
        config_data = _load_config_as_dict(config)
        config_data["output-format"] = output_format
        reporter = checker(module_name=paths, config=config_data)
    elif output_format:
        reporter = checker(module_name=paths, config={"output-format": output_format})
    elif config:
        reporter = checker(module_name=paths, config=config)
    else:
        reporter = checker(module_name=paths)

    if not exit_zero and reporter.has_messages():
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":  # pragma: no cover
    main()
