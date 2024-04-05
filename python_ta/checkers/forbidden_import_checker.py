"""Checker or use of forbidden imports.
"""

from __future__ import annotations

import os

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class ForbiddenImportChecker(BaseChecker):
    """A checker class to report on the disallowed imports in the file.
    Use options to specify the import modules that are allowed and the extra import modules."""

    name = "forbidden_import"
    msgs = {
        "E9999": (
            "You may not import %s.",
            "forbidden-import",
            "Used when you use import",
        )
    }
    options = (
        (
            "allowed-import-modules",
            {
                "default": (),
                "type": "csv",
                "metavar": "<modules>",
                "help": "Allowed names to be imported.",
            },
        ),
        (
            "extra-imports",
            {
                "default": (),
                "type": "csv",
                "metavar": "<extra-modules>",
                "help": "Extra allowed names to be imported.",
            },
        ),
        (
            "allow-local-imports",
            {
                "default": False,
                "type": "yn",
                "metavar": "<yn>",
                "help": "Allow local modules to be imported.",
            },
        ),
    )

    @only_required_for_messages("forbidden-import")
    def visit_import(self, node: nodes.Import) -> None:
        """visit an Import node"""
        local_files = self.get_allowed_local_files()

        temp = [
            name
            for name in node.names
            if name[0] not in self.linter.config.allowed_import_modules
            and name[0] not in self.linter.config.extra_imports
            and name[0] not in local_files
        ]

        if temp:
            self.add_message(
                "forbidden-import",
                node=node,
                args=("module " + ", ".join(map(lambda x: x[0], temp)),),
            )

    @only_required_for_messages("forbidden-import")
    def visit_importfrom(self, node: nodes.ImportFrom) -> None:
        """visit an ImportFrom node"""
        if (
            node.modname not in self.linter.config.allowed_import_modules
            and node.modname not in self.linter.config.extra_imports
            and node.modname not in self.get_allowed_local_files()
        ):
            # since name will be the combined form, e.g. math.sqrt, in the message we want just the imported name itself
            forbidden_imports = [
                name.split(".")[-1]
                for name in _get_full_import_names(node.modname, node.names)
                if name not in self.linter.config.allowed_import_modules
                and name not in self.linter.config.extra_imports
            ]
            if forbidden_imports:
                message = ", ".join(forbidden_imports) + " from module " + node.modname

                self.add_message("forbidden-import", node=node, args=(message,))

    @only_required_for_messages("forbidden-import")
    def visit_call(self, node: nodes.Call) -> None:
        if isinstance(node.func, nodes.Name):
            name = node.func.name
            # ignore the name if it's not a builtin (i.e. not defined in the
            # locals nor globals scope)
            if not (name in node.frame() or name in node.root()):
                if name == "__import__":
                    if (
                        node.args[0].value not in self.linter.config.allowed_import_modules
                        and node.args[0].value not in self.linter.config.extra_imports
                        and node.args[0].value not in self.get_allowed_local_files()
                    ):
                        args = ("module " + node.args[0].value,)
                        self.add_message("forbidden-import", node=node, args=args)

    def get_allowed_local_files(self) -> list:
        """
        Returns the list of the local files given by self.linter.current_file

        Returns empty list if current_file is not defined
        Returns empty list if local imports are not allowed
        """
        if self.linter.current_file is None:
            return []

        if not self.linter.config.allow_local_imports:
            return []

        return [
            f[:-3]
            for f in os.listdir(os.path.dirname(self.linter.current_file))
            if f.endswith(".py")
        ]


def register(linter: PyLinter) -> None:
    """Required method to auto register this checker"""
    linter.register_checker(ForbiddenImportChecker(linter))


def _get_full_import_names(modname: str, names: list[tuple[str, str]]) -> list:
    """Given a module name and a list of names imported from the module, return a list of strings
    in the form {module name}.{function name}.

    modname and names are in the format as provided from the corresponding attributes in the astroid.ImportFrom node
    """
    return [modname + "." + name[0] for name in names]
