"""Python Teaching Assistant

The goal of this module is to provide automated feedback to students in our
introductory Python courses, using static analysis of their code.

To run the checker, call the check function on the name of the module to check.

> import pyta
> pyta.check('mymodule')
"""
import importlib.util
import ast

def check(module_name):
    spec = importlib.util.find_spec(module_name)
    with open(spec.origin, 'r') as f:
        source = f.read()

    module_ast = ast.parse(source)

    visitor = PrintVisitor()
    visitor.visit(module_ast)


class PrintVisitor(ast.NodeVisitor):
    def visit(self, node, depth=0):
        print('  ' * depth + node.__class__.__name__)
        for child in ast.iter_child_nodes(node):
            self.visit(child, depth + 1)
