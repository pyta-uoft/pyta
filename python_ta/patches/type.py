"""Patch to add a transform for setting type constraints.
"""
from pylint.lint import PyLinter
from ..transforms.type_inference_visitor import TypeInferer


def patch_type_inference_transform():
    old_get_ast = PyLinter.get_ast

    def new_get_ast(self, filepath, modname):
        ast = old_get_ast(self, filepath, modname)
        if ast is not None:
            type_inferer = TypeInferer()
            env_transformer = type_inferer.environment_transformer()
            type_transformer = type_inferer.type_inference_transformer()
            try:
                env_transformer.visit(ast)
                type_transformer.visit(ast)
            except:
                pass
        return ast

    PyLinter.get_ast = new_get_ast
