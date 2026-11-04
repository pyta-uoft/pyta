import click

from .snapshot import run_with_snapshots


@click.group()
def main() -> None:
    """Run Python files with PythonTA debug features enabled."""


@main.command()
@click.argument("file", type=click.Path(exists=True, dir_okay=False))
def snapshot(file: str) -> None:
    """Run FILE with snapshot comments (# pyta: snapshot(...)) enabled."""
    run_with_snapshots(file)


if __name__ == "__main__":
    main()
