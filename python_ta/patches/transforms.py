"""Patch to add transforms for setting type constraints and creating control flow graphs.
"""

from pylint.lint import PyLinter

from ..cfg.visitor import CFGVisitor
from ..transforms.z3_visitor import Z3Visitor


def patch_ast_transforms(z3: bool):
    old_get_ast = PyLinter.get_ast

    def new_get_ast(self, filepath, modname, data):
        ast = old_get_ast(self, filepath, modname, data)
        if ast is not None:
            try:
                if z3:
                    ast = Z3Visitor().visitor.visit(ast)
                    ast.accept(CFGVisitor(options={"separate-condition-blocks": True}))
                else:
                    ast.accept(CFGVisitor())
            except:
                pass
        return ast

    PyLinter.get_ast = new_get_ast
