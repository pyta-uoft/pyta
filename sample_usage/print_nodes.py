"""Print out the source text corresponding to AST nodes.
"""
import astroid
import colorama
from colorama import Fore, Back, Style
import python_ta.transforms.setendings as setendings
import os 

colorama.init(strip=False, autoreset=True)

# Stying for each key part from, 
# (col_offset, fromlineno) to (end_col_offset, end_lineno).
MAIN_COL = Style.BRIGHT + Fore.WHITE + Back.BLACK


def wrap_color(code_string):
    """Wrap key parts in styling and resets."""
    return MAIN_COL + code_string + Back.RESET


def print_node(filename, node_class):
    """Print all nodes of the given class in the given file."""
    with open(filename) as f:
        content = f.read()
    source_lines = content.split('\n')
    module = astroid.parse(content)

    # Set end_lineno and end_col_offset for all nodes in `module`.
    ending_transformer = setendings.init_register_ending_setters()
    ending_transformer.visit(module)

    for node in module.nodes_of_class(node_class):
        if node.fromlineno == node.end_lineno:
            line = source_lines[node.fromlineno - 1]  # string
            out = [
                Style.DIM +
                line[:node.col_offset] +

                # The key part:
                MAIN_COL +
                line[node.col_offset : node.end_col_offset] +

                Style.DIM + Fore.RESET + Back.RESET +
                line[node.end_col_offset:]
            ]
        else:
            first_line = source_lines[node.fromlineno - 1]  # string
            middle_lines = source_lines[node.fromlineno: node.end_lineno - 1]  # list
            last_line = source_lines[node.end_lineno - 1]  # string

            if middle_lines:
                # For each item in the list of lines of strings,
                # add colorama style to middle like the first and last lines
                middle_lines = '\n'.join(list(map(wrap_color, middle_lines))) + '\n'
            else:
                middle_lines = ''  # coerce list to string

            if first_line:  # Add a spacing after first_line
                middle_lines = '\n' + middle_lines

            out = [
                Style.DIM + 
                first_line[:node.col_offset] +
                
                # The key part:
                MAIN_COL + 
                first_line[node.col_offset:] +

                Back.RESET + 
                middle_lines +

                MAIN_COL + 
                last_line[:node.end_col_offset] + 
                
                Style.DIM + Back.RESET +
                last_line[node.end_col_offset:]
            ]
        print('\n'.join(out))



if __name__ == '__main__':
    for node_class in astroid.ALL_NODE_CLASSES:
        print('=== {} ==='.format(node_class.__name__))
        file_location = 'nodes/' + node_class.__name__ + '.py'
        try:
            print_node(file_location, node_class)
        except FileNotFoundError:
            print('WARNING: No file for class {}'.format(node_class))
        except AttributeError:
            print('ERROR: for class {}'.format(node_class))

        print('')
