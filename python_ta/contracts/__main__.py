import os.path
import sys
import traceback
import types
from typing import List, TextIO, Tuple

import astroid
import click


@click.command()
@click.argument("main", type=click.File(mode="r"))
@click.argument("extra-mod-names", nargs=-1)
@click.option("--no-main", "-n", is_flag=True, default=True)
def check_contracts(main: TextIO, extra_mod_names: Tuple, no_main: bool):
    """Run python_ta.contracts.check_all_contracts() using the provided arguments

    MAIN the Python script as if you were to just run `python MAIN`
    EXTRA_MOD_NAMES are the module names to also have contracts checked.
        These are directly passed in, so the format is the module names as if you were importing
    NO_MAIN is whether to decorate main or not. No flag defaults to True.
    """
    contents = main.read()
    module_node = astroid.parse(contents)
    lines = contents.splitlines()

    if_main = _extract_if_main(module_node)

    if if_main:
        duck_main = ContractsRunnerModule("__main__", if_main, lines, extra_mod_names, no_main)

        true_main = sys.modules["__main__"]
        sys.modules["__main__"] = duck_main
        try:
            duck_main.run()
        except Exception:
            exception_message = traceback.format_exc()
            main_path = os.path.abspath(main.name)
            formatted_exception = exception_message.replace("<string>", main_path)
            sys.stderr.write(formatted_exception)

        sys.modules["__main__"] = true_main


class ContractsRunnerModule(types.ModuleType):
    """A pseudo module used for splitting up execution contexts to insert contract checking
    before the if __name__ == "__main__" entry point
    """

    def __init__(
        self,
        name: str,
        if_main: astroid.If,
        lines: List[str],
        extra_mod_names: Tuple,
        no_main: bool,
    ) -> None:
        super().__init__(name)

        split_point = if_main.lineno - 1
        self.before_main = "\n".join(lines[:split_point])
        self.after_main = "\n" * split_point + "\n".join(lines[split_point:])
        self.extra_mod_names = extra_mod_names
        self.no_main = no_main

        # not required but prevents __dict__ from being auto populated with all default builtins
        self.__builtins__ = globals()["__builtins__"]

    def run(self) -> None:
        exec(self.before_main, self.__dict__)
        import python_ta.contracts

        python_ta.contracts.check_all_contracts(*self.extra_mod_names, decorate_main=self.no_main)
        exec(self.after_main, self.__dict__)


def _extract_if_main(module_node: astroid.Module) -> astroid.If:
    if_nodes = module_node.nodes_of_class(astroid.If)
    return next(
        (node for node in if_nodes if node.test.as_string() == "__name__ == '__main__'"), None
    )


if __name__ == "__main__":
    check_contracts()
