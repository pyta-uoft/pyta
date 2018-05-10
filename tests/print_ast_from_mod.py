"""
Sanity checker to pretty print the abstract syntax tree (AST) structure.
"""
import sys
import astroid
from colorama import Back, Fore

USAGE = 'Usage: python print_ast.py <str representation of py file>'
FILL = '  '
# Unicode Box Drawing Characters.
CHAR_PIPE = '┃'
CHAR_TUBE = '━'


def walker(node, indent=''):
    """Recursively visit the ast in a preorder traversal."""

    node_name = str(node)[0:str(node).index('(')]
    value = None
    if hasattr(node, 'value'):
        if '(' in str(node.value):
            value = str(node.value)[0:str(node.value).index('(')]
        else:
            value = node.value

    name = node.name if hasattr(node, 'name') else None
    print('{}{} {} (name: {}, value: {})'.format(
        indent, CHAR_TUBE, node_name, name, value))

    lines = [line for line in node.as_string().split('\n')]
    for line in lines: 
        print(indent + FILL + '>>>' + Fore.BLUE + line + Fore.RESET)

    for child in node.get_children(): 
        walker(child, indent + FILL + CHAR_PIPE)


def print_ast(ast_mod):
    print('Note: code in the ">>>" section is an approximation.\n')
    for node in ast_mod.body:
        walker(node, CHAR_PIPE)
    print('┣' + CHAR_TUBE * 60 + '┫')
    print('')

