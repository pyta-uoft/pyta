"""
Check for missing return statements in non-None functions.
"""

from typing import Optional

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class MissingReturnChecker(BaseChecker):
    name = "missing-return-statement"
    msgs = {
        "R9711": (
            "Missing return statement in function `%s`",
            "missing-return-statement",
            "Used when a function does not have a return statement and whose return type is not None",
        ),
    }
    options = (
        (
            "z3",
            {
                "default": False,
                "type": "yn",
                "metavar": "<y or n>",
                "help": "Use Z3 to restrict control flow checks to paths that are logically feasible.",
            },
        ),
    )

    def __init__(self, linter: Optional[PyLinter] = None) -> None:
        super().__init__(linter=linter)

    @only_required_for_messages("missing-return-statement")
    def visit_functiondef(self, node) -> None:
        """Visit a function definition"""
        self._check_return_statements(node)

    def _check_return_statements(self, node) -> None:
        """
        Check for missing returns based on CFG
        if the function has a return type annotation or has at least one
        non-None return values.
        """
        if isinstance(node.returns, nodes.Const) and node.returns.value is None:
            return

        has_return_annotation = node.returns is not None
        has_return_value = False

        # get the blocks connected to the end of cfg
        end = node.cfg.end
        # ignore unfeasible edges for missing return if z3 option is on
        end_blocks = [
            edge.source
            for edge in end.predecessors
            if not self.linter.config.z3 or edge.is_feasible
        ]

        # gather the return statement of each code block
        return_statements = {}
        for block in end_blocks:
            return_statements[block] = None
            statement = block.statements[-1]
            if isinstance(statement, nodes.Return):
                return_statements[block] = statement
                # if the return statement is not `return` or `return None`
                if not (
                    statement.value is None
                    or isinstance(statement.value, nodes.Const)
                    and statement.value.value is None
                ):
                    has_return_value = True
            elif isinstance(statement, nodes.Raise):
                return_statements[block] = statement

        # check for missing returns
        if has_return_annotation or has_return_value:
            for block, statement in return_statements.items():
                if statement is None:
                    # ignore unfeasible edges for missing return if z3 option is on
                    if self.linter.config.z3 and (
                        not block.is_feasible
                        or not any(
                            edge.is_feasible for edge in block.successors if edge.target is end
                        )
                    ):
                        continue

                    # For rendering purpose:
                    # line: the line where the error occurs, used to calculate indentation
                    # end_line: the line to insert the error message

                    # For `while` and `for` loops, line and end_line need to set to those of the parent node
                    # to make sure the message is rendered at the end of the loop
                    last_statement = block.statements[-1]
                    line = last_statement.lineno
                    end_line = last_statement.end_lineno
                    if isinstance(last_statement.parent, (nodes.While, nodes.For, nodes.If)):
                        line = last_statement.parent.lineno
                        end_line = last_statement.parent.end_lineno

                    self.add_message(
                        "missing-return-statement",
                        node=node,
                        line=line,
                        end_lineno=end_line,
                        args=node.name,
                    )


def register(linter: PyLinter) -> None:
    linter.register_checker(MissingReturnChecker(linter))
