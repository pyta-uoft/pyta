import click

from .cfg_generator import generate_cfg


def parse_visitor_options(options_str):
    """Parse comma-separated key=value pairs."""
    if not options_str:
        return {}

    options = {}

    if "separate-condition-blocks=" in options_str:
        if "separate-condition-blocks=true" in options_str:
            options["separate-condition-blocks"] = True
        elif "separate-condition-blocks=false" in options_str:
            options["separate-condition-blocks"] = False
        else:
            raise ValueError("separate-condition-blocks must be 'true' or 'false'")

    if "functions=" in options_str:
        start = options_str.find("functions=") + len("functions=")
        value = options_str[start:].strip().strip("'\"")
        if not value:
            raise ValueError("functions cannot be empty")
        options["functions"] = [f.strip() for f in value.split(",")]

    return options


@click.command()
@click.argument("mod")
@click.option(
    "--auto-open", is_flag=True, default=False, help="automatically opens the cfg in the browser"
)
@click.option(
    "--visitor-options",
    type=str,
    help="Comma-separated key=value pairs for visitor options, e.g., "
    "\"separate-condition-blocks=true,functions='foo,bar,baz'\"",
)
def main(mod, auto_open, visitor_options):
    """Generate a Control Flow Graph for a Python file."""
    if visitor_options:
        try:
            visitor_options = parse_visitor_options(visitor_options)
        except ValueError as error:
            click.echo(f"Error: {error}", err=True)
            raise click.Abort()

    generate_cfg(mod=mod, auto_open=auto_open, visitor_options=visitor_options)


if __name__ == "__main__":
    main()
