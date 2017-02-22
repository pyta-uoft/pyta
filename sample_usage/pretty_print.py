"""
Sanity checker to pretty print the ast structure of a file, 
to see the properties: fromlineno, end_lineno, col_offset, end_col_offset.
Run from /pyta/ dir: python pretty_print.py <your-file-here.py>
"""
import sys
import astroid
import python_ta.transforms.setendings as setendings
from colorama import Back, Fore

# Unicode Box Drawing Characters.
# https://en.wikipedia.org/wiki/Box-drawing_character#Unicode
CHAR_PIPE = '┃'
CHAR_TUBE = '━'
FILL = '  '

def _print_line(pre, v1, n1, v2, n2):
    """(string, string, int, string, int)
    Print values, somewhat aligned, e.g.) 
        fromlineno:        2 ... end_lineno:        2
        col_offset:       24 ... end_col_offset:   25
    """
    print('{}{:<15} {:>4} ... {:<15} {:>4}'.format(pre, v1, n1, v2, n2))


def _walk_astroid_ast(node, source_lines, indent=''):
    """Recursively visit the ast in a preorder traversal."""

    #### Explore which nodes have the 'name' or 'value' property.
    value = node.value if hasattr(node, 'value') else None
    name = node.name if hasattr(node, 'name') else None
    # print('{}{} {}, name: {},  value: {},  [parent: {}]'\
    #     .format(indent, CHAR_TUBE, node, name, value, node.parent))
    print('{}{} {}, name: {},  value: {}'\
        .format(indent, CHAR_TUBE, node, name, value))

    #### Note: some of the attributes could not be declared, or initialized to 'None'.
    _print_line(indent + FILL, 'fromlineno:', node.fromlineno, 'end_lineno:', node.end_lineno)
    _print_line(indent + FILL, 'col_offset:', node.col_offset, 'end_col_offset:', node.end_col_offset)

    #### Print the source code. (note: fromlineno, end_lineno are 1-indexed).
    lines = [line for line in node.as_string().split('\n')]
    node_lines = list(source_lines[node.fromlineno-1:node.end_lineno])
    node_lines[-1] = node_lines[-1][0:node.end_col_offset]
    node_lines[0] = node_lines[0][node.col_offset:]
    for line in lines: print(indent + FILL + '>>>' + Fore.BLUE + line + Fore.RESET)
    for line in node_lines: print(indent + FILL + '>>>' + Fore.YELLOW + line + Fore.RESET)

    #### Recurse.
    for child in node.get_children(): _walk_astroid_ast(child, source_lines, indent + FILL + CHAR_PIPE)


if __name__ == '__main__':
    if len(sys.argv) >= 2:
        with open(sys.argv[1]) as file:
            # visit_astroid(astroid.parse(file.read()))
            file_contents = file.read()
            astroid_module = astroid.parse(file_contents)
            source_lines = file_contents.split('\n')
            # Register all the transform functions.
            ending_transformer = setendings.init_register_ending_setters(source_lines)

            # Traverse the transformed tree, and pretty print it..
            assert isinstance(astroid_module, astroid.scoped_nodes.Module), \
            'ERROR: must pass astroid module to visit_astroid().'

            if len(sys.argv) is 3:
                print("repr_tree:\n==========\n", astroid_module.body[0].repr_tree(True))
                print("\n")

            # Apply all transforms to the parsed module.
            ending_transformer.visit(astroid_module)

            # 'astroid_module.body' contains all the top-level nodes.
            print('\nNote: the code string in the section indicated by ">>>" may not be accurate.\n')
            for node in astroid_module.body:
                _walk_astroid_ast(node, source_lines, CHAR_PIPE)
                print('┣' + CHAR_TUBE * 70 + '┫')
            print('')
    else:
        logging.error("⛔️ Use like: python pretty_print.py <your-file-here.py>")
