from typing import TextIO, Tuple

import astroid
import click


@click.command()
@click.argument("main", type=click.File(mode="r"))
@click.argument("extra-mod-names", nargs=-1)
@click.option("--no-main", "-n", is_flag=True, default=True)
def run_contracts(main: TextIO, extra_mod_names: Tuple, no_main: bool):
    """Run python_ta.contracts.check_all_contracts() using the provided arguments

    MAIN the Python script as if you were to just run `python MAIN`
    EXTRA_MOD_NAMES are the module names to also have contracts checked.
        These are directly passed in, so the format is the module names as if you were importing
    NO_MAIN is whether to decorate main or not. No flag defaults to True.
    """
    contents = main.read()
    module_node = astroid.parse(contents)

    if_main = _extract_if_main(module_node)
    if if_main:
        import_statement = _build_import()
        if_main.body.insert(0, import_statement)
        contracts_call = _build_contracts_call(extra_mod_names, decorate_main=no_main)
        if_main.body.insert(1, contracts_call)

    modified_main_contents = module_node.as_string()

    exec(modified_main_contents, globals())


def _build_import() -> astroid.NodeNG:
    return astroid.extract_node("import python_ta.contracts")


def _build_contracts_call(mod_names: Tuple, decorate_main: bool) -> astroid.NodeNG:
    mod_names_str = ", ".join((f"'{name}'" for name in mod_names))
    function_args = f"{mod_names_str}{', ' if mod_names_str else ''}decorate_main={decorate_main}"
    return astroid.extract_node(f"python_ta.contracts.check_all_contracts({function_args})")


def _extract_if_main(module_node: astroid.Module) -> astroid.If:
    if_nodes = module_node.nodes_of_class(astroid.If)
    return next(
        (node for node in if_nodes if node.test.as_string() == "__name__ == '__main__'"), None
    )


if __name__ == "__main__":
    run_contracts()
