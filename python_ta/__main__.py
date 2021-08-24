import sys
from typing import List, Optional

import click

from python_ta import check_all, check_errors

CONTEXT_SETTINGS = dict(help_option_names=["-h", "--help"])


@click.command(context_settings=CONTEXT_SETTINGS)
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
def main(config: Optional[str], errors_only: bool, filenames: List[str], exit_zero: bool) -> None:
    """A code checking tool for teaching Python.

    FILENAMES can be a string of a directory, or file to check (`.py` extension optional) or
    a list of strings of directories or files.
    """
    # `config` is None if `-c` flag is not set
    checker = check_errors if errors_only else check_all
    paths = [click.format_filename(fn) for fn in filenames]
    reporter = checker(module_name=paths, config=config)

    if not exit_zero and reporter.has_messages():
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()
