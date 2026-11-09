import shlex
from typing import Any, Optional

import click

from .snapshot import run_with_snapshots


@click.group()
def main() -> None:
    """Run Python files with PythonTA debug features enabled."""


@main.command()
@click.argument("file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--save/--no-save",
    default=True,
    show_default=True,
    help="Whether to save a MemoryViz diagram for each snapshot.",
)
@click.option(
    "--memory-viz-args",
    help='Options passed to the MemoryViz CLI, as one quoted string (e.g. "--width 1000").',
)
@click.option("--memory-viz-version", help="Version of MemoryViz to use.")
@click.option(
    "--include-frame",
    "include_frames",
    multiple=True,
    help="Only capture variables from this function. Can be repeated.",
)
@click.option(
    "--exclude-frame",
    "exclude_frames",
    multiple=True,
    help="Do not capture variables from this function. Can be repeated.",
)
@click.option(
    "--exclude-var",
    "exclude_vars",
    multiple=True,
    help="Do not capture this variable. Can be repeated.",
)
def snapshot(
    file: str,
    save: bool,
    memory_viz_args: Optional[str],
    memory_viz_version: Optional[str],
    include_frames: tuple[str, ...],
    exclude_frames: tuple[str, ...],
    exclude_vars: tuple[str, ...],
) -> None:
    """Run FILE with snapshot comments (# pyta: snapshot(...)) enabled.

    Options set the default arguments for every snapshot comment. Arguments given in a
    snapshot comment override them.
    """
    kwargs: dict[str, Any] = {"save": save}
    if memory_viz_args is not None:
        kwargs["memory_viz_args"] = shlex.split(memory_viz_args)
    if memory_viz_version is not None:
        kwargs["memory_viz_version"] = memory_viz_version
    if include_frames:
        kwargs["include_frames"] = list(include_frames)
    if exclude_frames:
        kwargs["exclude_frames"] = list(exclude_frames)
    if exclude_vars:
        kwargs["exclude_vars"] = list(exclude_vars)

    run_with_snapshots(file, **kwargs)


if __name__ == "__main__":
    main()
