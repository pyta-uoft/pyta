"""
Sanity checker to pretty print the abstract syntax tree (AST) structure.
"""
import sys
import astroid
from colorama import Back, Fore

USAGE = 'Usage: python -m sample_usage.print_ast <your-file.py>'
FILL = '  '
# Unicode Box Drawing Characters.
CHAR_PIPE = '┃'
CHAR_TUBE = '━'


def walker(node, source_lines, indent=''):
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
        walker(child, source_lines, indent + FILL + CHAR_PIPE)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print(USAGE)
        exit()

    with open(sys.argv[1]) as file:
        file_contents = file.read()
        astroid_module = astroid.parse(file_contents)
        source_lines = file_contents.split('\n')
        print('Note: code in the ">>>" section is an approximation.\n')
        for node in astroid_module.body:
            walker(node, source_lines, CHAR_PIPE)
            print('┣' + CHAR_TUBE * 60 + '┫')
        print('')
