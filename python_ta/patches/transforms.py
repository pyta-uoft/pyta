"""Patch to add transforms for setting type constraints and creating control flow graphs.
"""

import logging

from pylint.lint import PyLinter

from ..cfg.visitor import CFGVisitor


def patch_ast_transforms(z3: bool):
    old_get_ast = PyLinter.get_ast

    def new_get_ast(self, filepath, modname, data):
        ast = old_get_ast(self, filepath, modname, data)
        if ast is None:
            return None

        # Run the Z3Visitor
        if z3:
            try:
                from ..transforms.z3_visitor import Z3Visitor

                ast = Z3Visitor().visitor.visit(ast)
            except Exception as e:
                logging.warning(f"Could not run Z3Visitor: {e}")

        # Run the CFGVisitor
        try:
            ast.accept(CFGVisitor())
        except Exception as e:
            logging.warning(f"Could not run Z3Visitor: {e}")

        return ast

    PyLinter.get_ast = new_get_ast
