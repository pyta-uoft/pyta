from typing import Any, Dict, List, Optional, Union

import click

from .cfg_generator import generate_cfg


def split_by_comma_if_outside_quotes(options_str: str) -> List[str]:
    """Split string by commas, but not commas inside quotes."""
    parts: List[str] = []
    current_part: List[str] = []
    in_quotes: bool = False
    quote_char: Optional[str] = None

    for char in options_str:
        if char in ('"', "'") and not in_quotes:
            in_quotes = True
            quote_char = char
            current_part.append(char)
        elif char == quote_char and in_quotes:
            in_quotes = False
            quote_char = None
            current_part.append(char)
        elif char == "," and not in_quotes:
            parts.append("".join(current_part).strip())
            current_part = []
        else:
            current_part.append(char)

    if current_part:
        parts.append("".join(current_part).strip())

    return parts


def parse_visitor_options(options_str: str) -> Dict[str, Union[bool, List[str], str]]:
    """Parse comma-separated key=value pairs."""
    if not options_str:
        return {}

    parts = split_by_comma_if_outside_quotes(options_str)

    options: Dict[str, Union[bool, List[str], str]] = {}
    for part in parts:
        if "=" not in part:
            continue

        key, value = part.split("=", 1)
        value = value.strip()

        # Strip any quotes if present
        if value.startswith(("'", '"')) and value.endswith(("'", '"')):
            value = value[1:-1]

        # Type conversions
        if value.lower() in ("true", "false"):
            options[key] = value.lower() == "true"
        elif "," in value:
            options[key] = [v.strip() for v in value.split(",")]
        else:
            options[key] = value

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
def main(mod: str, auto_open: bool, visitor_options: Optional[str]) -> None:
    """Generate a Control Flow Graph for a Python file."""
    parsed_options: Optional[Dict[str, Any]] = None

    if visitor_options:
        try:
            parsed_options = parse_visitor_options(visitor_options)
        except ValueError as error:
            click.echo(f"Error: {error}", err=True)
            raise click.Abort()

    generate_cfg(mod=mod, auto_open=auto_open, visitor_options=parsed_options)


if __name__ == "__main__":
    main()
