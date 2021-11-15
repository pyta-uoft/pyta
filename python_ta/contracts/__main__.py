import os.path
import sys
import traceback
import types
from typing import List, TextIO, Tuple

import click

from . import check_all_contracts


@click.command()
@click.argument("file", type=click.File(mode="r"))
@click.option("--extra-mod-name", "-e", multiple=True, help="Name of imported module to also check")
@click.option("--no-decorate-main", is_flag=True, default=True, help="Disable decorating FILE")
def check_contracts(file: TextIO, extra_mod_name: Tuple, no_decorate_main: bool):
    """Run FILE as Python script with PythonTA's contract checking enabled.

    FILE the Python script as if you were to just run `python FILE`
    """
    contents = file.read()
    lines = contents.splitlines()

    main_lineno = _find_main_lineno(lines)

    if main_lineno:
        duck_main = ContractsRunnerModule(
            "__main__", main_lineno, lines, extra_mod_name, no_decorate_main
        )

        true_main = sys.modules["__main__"]
        sys.modules["__main__"] = duck_main
        try:
            duck_main.run()
        except SystemExit as se:
            sys.stderr.write(_formatted_traceback(file.name))
            sys.exit(se.args[0])
        except Exception:
            sys.stderr.write(_formatted_traceback(file.name))
            sys.exit(1)

        sys.modules["__main__"] = true_main


class ContractsRunnerModule(types.ModuleType):
    """A pseudo module used for splitting up execution contexts to insert contract checking
    before the if __name__ == "__main__" entry point
    """

    def __init__(
        self,
        name: str,
        main_lineno: int,
        lines: List[str],
        extra_mod_names: Tuple,
        no_main: bool,
    ) -> None:
        super().__init__(name)

        split_point = main_lineno - 1
        self.before_main = "\n".join(lines[:split_point])
        self.after_main = "\n" * split_point + "\n".join(lines[split_point:])
        self.extra_mod_names = extra_mod_names
        self.no_main = no_main

        # not required but prevents __dict__ from being auto populated with all default builtins
        self.__builtins__ = globals()["__builtins__"]

    def run(self) -> None:
        exec(self.before_main, self.__dict__)
        check_all_contracts(*self.extra_mod_names, decorate_main=self.no_main)
        exec(self.after_main, self.__dict__)


def _formatted_traceback(file_name) -> str:
    """Gets current traceback as string while removing run and exec frames and replacing
    the default exec context name "<string>" with the ran file name."""
    exception_traceback = sys.exc_info()[2]

    stack_size = len(traceback.extract_tb(exception_traceback))
    # ignores first two frames of traceback (module runner and exec frames)
    exception_message = traceback.format_exc(limit=-(stack_size - 2))

    main_path = os.path.abspath(file_name)
    formatted_exception = exception_message.replace("<string>", main_path)
    return formatted_exception


def _find_main_lineno(lines: list[str]) -> int:
    for lineno, line in enumerate(lines, start=1):
        if _has_main_check(line):
            return lineno
    return 0


def _has_main_check(line: str) -> bool:
    if line.strip() == "":
        return False
    keyword, *condition = line.split()
    spaceless_condition = "".join(condition)
    return (
        keyword == "if"
        and line.startswith(keyword)
        and (
            spaceless_condition == "__name__=='__main__':"
            or spaceless_condition == '__name__=="__main__":'
        )
    )


if __name__ == "__main__":
    check_contracts()
