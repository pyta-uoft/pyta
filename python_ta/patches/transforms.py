"""Patch to add transforms for setting type constraints and creating control flow graphs.
"""
from pylint.lint import PyLinter

from ..cfg.visitor import CFGVisitor


def patch_ast_transforms():
    old_get_ast = PyLinter.get_ast

    def new_get_ast(self, filepath, modname, data):
        ast = old_get_ast(self, filepath, modname, data)
        if ast is not None:
            try:
                ast.accept(CFGVisitor())
            except:
                pass
        return ast

    PyLinter.get_ast = new_get_ast
