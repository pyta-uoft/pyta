import json

import click

from .cfg_generator import generate_cfg


@click.command()
@click.argument("mod")
@click.option(
    "--auto-open", is_flag=True, default=False, help="automatically opens the cfg in the browser"
)
@click.option(
    "--visitor-options",
    type=str,
    help='JSON string of visitor options, eg. \'{"separate-condition-blocks": true, "functions": ["MyClass.foo"]}\'',
)
def main(mod, auto_open, visitor_options):
    """Generate a Control Flow Graph for a Python file."""
    if visitor_options:
        try:
            visitor_options = json.loads(visitor_options)
        except json.JSONDecodeError as error:
            click.echo(f"Error: Invalid JSON for visitor-options: {error}", err=True)
            raise click.Abort()

    generate_cfg(mod=mod, auto_open=auto_open, visitor_options=visitor_options)


if __name__ == "__main__":
    main()
