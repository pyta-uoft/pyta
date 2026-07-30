from __future__ import annotations

import shutil
import sys
import tempfile
from os import path
from typing import Optional

import click

from python_ta import __version__, check_all, check_errors
from python_ta.config import DEFAULT_CONFIG_LOCATION

CONTEXT_SETTINGS = dict(help_option_names=["-h", "--help"])


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
    "filenames", nargs=-1, type=click.Path(dir_okay=True, resolve_path=True, allow_dash=True)
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
@click.option(
    "--stdin",
    is_flag=True,
    help="Read file contents from stdin instead of a file",
    default=False,
)
def main(
    version: bool,
    config: Optional[str],
    errors_only: bool,
    filenames: list[str],
    exit_zero: bool,
    generate_config: bool,
    output_format: Optional[str],
    stdin: bool,
) -> None:
    """A code checking tool for teaching Python.
    FILENAMES can be a string of a directory, or file to check (`.py` extension optional) or
    a list of strings of directories or files. Pass - as a filename or use --stdin to read
    from standard input.
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
    use_stdin = stdin or (len(filenames) == 1 and filenames[0] == "-")

    if use_stdin:
        # Write the contents of stdin to a temporary file
        # TODO: Replace `delete=False` with `delete_on_close=False` after PythonTA
        # no longer supports Python 3.11 and earlier. This will allow the temporary
        # file to be cleaned up automatically by `NamedTemporaryFile`.
        with tempfile.NamedTemporaryFile(
            mode="w", prefix="stdin_", suffix=".py", delete=False, encoding="utf-8"
        ) as temp_file:
            shutil.copyfileobj(sys.stdin, temp_file)
            temp_file.flush()
            reporter = _invoke_checker(checker, [temp_file.name], config, output_format)
        # Clean up the temporary file
        path.os.unlink(temp_file.name)

    else:
        paths = [click.format_filename(fn) for fn in filenames]
        reporter = _invoke_checker(checker, paths, config, output_format)

    if not exit_zero and reporter.has_messages():
        sys.exit(1)
    else:
        sys.exit(0)


def _invoke_checker(checker, paths, config, output_format):
    """Invoke the checker with the appropriate arguments based on the provided config and output_format."""
    if output_format and config:
        # If both specified, use the config file and override the output format
        return checker(
            module_name=paths,
            config=config,
            pylint_args=["--output-format", output_format],
        )
    elif output_format:
        return checker(module_name=paths, config={"output-format": output_format})
    elif config:
        return checker(module_name=paths, config=config)
    else:
        return checker(module_name=paths)


if __name__ == "__main__":  # pragma: no cover
    main()
