"""
Sanity checker to pretty print the ast structure of a file, 
to see the properties: fromlineno, end_lineno, col_offset, end_col_offset.
Run from /pyta/ dir: python pretty_print.py <your-file-here.py>
"""
import sys
import astroid
import python_ta.transforms.setendings as setendings

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


def _walk_astroid_ast(node, indent=''):
    """Recursively visit the ast in a preorder traversal."""

    #### Explore which nodes have the 'name' or 'value' property.
    value = node.value if hasattr(node, 'value') else None
    name = node.name if hasattr(node, 'name') else None
    print('{}{} {}, name: {},  value: {},  [parent: {}]'\
        .format(indent, CHAR_TUBE, node, name, value, node.parent))

    #### Note: some of the attributes could not be declared, or initialized to 'None'.
    _print_line(indent + FILL, 'fromlineno:', node.fromlineno, 'end_lineno:', node.end_lineno)
    _print_line(indent + FILL, 'col_offset:', node.col_offset, 'end_col_offset:', node.end_col_offset)

    #### Get the widest line in the source code.
    lines = [line for line in node.as_string().split('\n')]
    max_width_line = max(lines, key=len)
    max_width = len(max_width_line)
    print('{}line max_width: {}, ["{}"]'.format(indent + FILL, max_width, max_width_line))

    #### Print the source code.
    for line in lines: print(indent + FILL + '>>>' + line)

    #### Recurse.
    for child in node.get_children(): _walk_astroid_ast(child, indent + FILL + CHAR_PIPE)


if __name__ == '__main__':
    if len(sys.argv) >= 2:
        with open(sys.argv[1]) as file:
            # visit_astroid(astroid.parse(file.read()))
            file_contents = file.read()
            astroid_module = astroid.parse(file_contents)
            # Register all the transform functions.
            ending_transformer = setendings.init_register_ending_setters(file_contents.split('\n'))

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
                _walk_astroid_ast(node, CHAR_PIPE)
                print('┣' + CHAR_TUBE * 70 + '┫')
            print('')
    else:
        logging.error("⛔️ Use like: python pretty_print.py <your-file-here.py>")
