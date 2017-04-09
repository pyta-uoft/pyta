"""Patch to add a transform for setting type constraints.
"""
from pylint.lint import PyLinter
from ..transforms.type_inference_visitor import register_type_constraints_setter, environment_transformer


def patch_type_inference_transform():
    old_get_ast = PyLinter.get_ast

    def new_get_ast(self, filepath, modname):
        ast = old_get_ast(self, filepath, modname)
        env_transformer = environment_transformer()
        env_transformer.visit(ast)
        type_transformer = register_type_constraints_setter()
        type_transformer.visit(ast)
        return ast

    PyLinter.get_ast = new_get_ast
