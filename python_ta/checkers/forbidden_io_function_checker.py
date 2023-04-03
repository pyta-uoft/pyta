"""checker for use of I/O functions.
"""

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages

from python_ta.utils import _is_in_main

FORBIDDEN_BUILTIN = ["input", "print", "open"]


class IOFunctionChecker(BaseChecker):
    name = "IO_Function"
    msgs = {
        "E9998": (
            "Used input/output function %s",
            "forbidden-IO-function",
            'Used when you use the I/O functions "print", "open" or "input". These '
            "functions should not be used except where specified by your instructor.",
        )
    }
    options = (
        (
            "forbidden-io-functions",
            {
                "default": FORBIDDEN_BUILTIN,
                "type": "csv",
                "metavar": "<builtin function names>",
                "help": "List of built-in function names that should not be used.",
            },
        ),
        (
            "allowed-io",
            {
                "default": (),
                "type": "csv",
                "metavar": "<forbidden io>",
                "help": "Functions where an I/O function may be used.",
            },
        ),
    )

    # this is important so that your checker is executed before others
    priority = -1

    @only_required_for_messages("forbidden-IO-function")
    def visit_call(self, node):
        if isinstance(node.func, nodes.Name):
            name = node.func.name
            # ignore the name if it's not a builtin (i.e. not defined in the
            # locals nor globals scope)
            if not (name in node.frame() or name in node.root()):
                scope = node.scope()
                scope_parent = scope.parent

                if (
                    isinstance(scope_parent, nodes.ClassDef)
                    and isinstance(scope, nodes.FunctionDef)
                    and (scope_parent.name + "." + scope.name) not in self.linter.config.allowed_io
                ):
                    if name in self.linter.config.forbidden_io_functions:
                        self.add_message("forbidden-IO-function", node=node, args=name)
                elif (
                    isinstance(scope_parent, nodes.Module)
                    and isinstance(scope, nodes.FunctionDef)
                    and scope.name not in self.linter.config.allowed_io
                ):
                    if name in self.linter.config.forbidden_io_functions:
                        self.add_message("forbidden-IO-function", node=node, args=name)
                elif isinstance(scope, nodes.Module) and not _is_in_main(node):
                    if name in self.linter.config.forbidden_io_functions:
                        self.add_message("forbidden-IO-function", node=node, args=name)


def register(linter):
    linter.register_checker(IOFunctionChecker(linter))
