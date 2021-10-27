import os.path
import sys
import traceback
import types
from typing import Any, Dict, TextIO, Tuple

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
        split_point = if_main.lineno - 1
        before_main = "\n".join(lines[:split_point])
        after_main = "\n" * split_point + "\n".join(lines[split_point:])

        line1 = f"exec(__before_main)\n"
        line2 = "import python_ta.contracts\n"
        line3 = "python_ta.contracts.check_all_contracts(*__extra_mods, decorate_main=__no_main)\n"
        line4 = f"exec(__after_main)\n"
        exec_content = line1 + line2 + line3 + line4

        extras = {
            "__before_main": before_main,
            "__after_main": after_main,
            "__no_main": no_main,
            "__extra_mods": extra_mod_names,
            "__builtins__": globals()["__builtins__"],
            "__name__": "__main__",
        }
        duck_main = DuckModule("__main__", extras, exec_content)

        true_main = sys.modules["__main__"]
        sys.modules["__main__"] = duck_main
        try:
            duck_main.run()
        except Exception:
            exception_message = traceback.format_exc()

            formatted_exception = exception_message.replace("<string>", "run context", 1)
            main_path = os.path.abspath(main.name)
            formatted_exception = formatted_exception.replace("<string>", main_path)
            sys.stderr.write(formatted_exception)

        sys.modules["__main__"] = true_main


class DuckModule(types.ModuleType):
    """A pseudo module used for syncing execution and module contexts"""

    def __init__(self, name: str, default_globals: Dict[str, Any], content: str) -> None:
        super().__init__(name)
        self.content = content
        for key, value in default_globals.items():
            setattr(self, key, value)

    def run(self) -> None:
        exec(self.content, self.__dict__)


def _extract_if_main(module_node: astroid.Module) -> astroid.If:
    if_nodes = module_node.nodes_of_class(astroid.If)
    return next(
        (node for node in if_nodes if node.test.as_string() == "__name__ == '__main__'"), None
    )


if __name__ == "__main__":
    check_contracts()
