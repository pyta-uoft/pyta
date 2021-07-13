import click
from python_ta import check_all, check_errors

CONTEXT_SETTINGS = dict(help_option_names=['-h', '--help'])

@click.command(context_settings=CONTEXT_SETTINGS)
@click.option('-c', '--config', type=click.Path(exists=True, dir_okay=False, resolve_path=True), help="python_ta configuration file")
@click.option('-E', '--errors-only', is_flag=True, help="Displays errors only", default=False)
@click.argument('filenames', nargs=-1, type=click.Path(exists=True, dir_okay=True, resolve_path=True))
def main(config, errors_only, filenames):
    """A code checking tool for teaching Python.

    FILENAMES can be a string of a directory, or file to check (`.py` extension optional) or
    a list of strings of directories or files.
    """
    # `config` is None if `-c` flag is not set
    checker = check_errors if errors_only else check_all
    paths = [click.format_filename(fn) for fn in filenames]
    checker(module_name=paths, config=config)

if __name__ == '__main__':
    main()
