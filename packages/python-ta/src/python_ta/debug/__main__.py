import shlex
from typing import Any, Optional

import click

from .snapshot import run_with_snapshots


def _split_comma_list(
    _ctx: click.Context, _param: click.Parameter, value: Optional[str]
) -> Optional[list[str]]:
    """Split a comma-separated option value into a list of non-empty, stripped strings."""
    if value is None:
        return None
    return [item.strip() for item in value.split(",") if item.strip()]


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
    callback=_split_comma_list,
    help="Only capture variables from the given functions, as a comma-separated list "
    "(e.g. func1,func2).",
)
@click.option(
    "--exclude-frame",
    "exclude_frames",
    callback=_split_comma_list,
    help="Do not capture variables from the given functions, as a comma-separated list "
    "(e.g. func1,func2).",
)
@click.option(
    "--exclude-var",
    "exclude_vars",
    callback=_split_comma_list,
    help="Do not capture the given variables, as a comma-separated list (e.g. x,y).",
)
def snapshot(
    file: str,
    save: bool,
    memory_viz_args: Optional[str],
    memory_viz_version: Optional[str],
    include_frames: Optional[list[str]],
    exclude_frames: Optional[list[str]],
    exclude_vars: Optional[list[str]],
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
        kwargs["include_frames"] = include_frames
    if exclude_frames:
        kwargs["exclude_frames"] = exclude_frames
    if exclude_vars:
        kwargs["exclude_vars"] = exclude_vars

    run_with_snapshots(file, **kwargs)


if __name__ == "__main__":
    main()
