from typing import TextIO, Tuple

import astroid
import click


@click.command()
@click.argument("main", type=click.File(mode="r"))
@click.argument("extra-mod-names", nargs=-1)
def run_contracts(main: TextIO, extra_mod_names: Tuple):
    contents = main.read()
    module_node = astroid.parse(contents)

    if_main = _extract_if_main(module_node)
    import_statement = _build_import()
    if_main.body.insert(0, import_statement)
    contracts_call = _build_contracts_call(extra_mod_names)
    if_main.body.insert(1, contracts_call)

    modified_main_contents = module_node.as_string()

    exec(modified_main_contents, globals())


def _build_import() -> astroid.NodeNG:
    return astroid.extract_node("import python_ta.contracts")


def _build_contracts_call(mod_names: Tuple) -> astroid.NodeNG:
    mod_names_str = ", ".join((f"'{name}'" for name in mod_names))
    return astroid.extract_node(f"python_ta.contracts.check_all_contracts({mod_names_str})")


def _extract_if_main(module_node: astroid.Module) -> astroid.If:
    if_nodes = module_node.nodes_of_class(astroid.If)
    return next(node for node in if_nodes if node.test.as_string() == "__name__ == '__main__'")


if __name__ == "__main__":
    run_contracts()
