"""Print out the source text corresponding to AST nodes.
"""
import astroid
import colorama
from colorama import Fore, Back, Style
import python_ta.transforms.setendings as setendings
import os 

colorama.init(strip=False)


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
            line = source_lines[node.fromlineno - 1]
            out = [Style.DIM +
                   line[:node.col_offset] +
                   Style.BRIGHT + Fore.WHITE + Back.BLACK +
                   line[node.col_offset:node.end_col_offset] +
                   Style.DIM +
                   line[node.end_col_offset:] + Style.RESET_ALL]
        else:
            first_line = source_lines[node.fromlineno - 1]
            last_line = source_lines[node.end_lineno - 1]
            middle_lines = source_lines[node.fromlineno: node.end_lineno - 1]

            out = (
                [Style.DIM +
                 first_line[:node.col_offset] +
                 Style.BRIGHT + Fore.WHITE + Back.BLACK +
                 first_line[node.col_offset:]] +
                middle_lines +
                [last_line[:node.end_col_offset] +
                 Style.DIM +
                 last_line[node.end_col_offset:] +
                 Style.RESET_ALL])
        print('\n'.join(out))



if __name__ == '__main__':
    for node_class in astroid.ALL_NODE_CLASSES:
        print('=== {} ==='.format(node_class.__name__))
        file_location = 'nodes/' + node_class.__name__ + '.py'
        try:
            print_node(file_location, node_class)
        except FileNotFoundError:
            print('ERROR: No file for class {}'.format(node_class))
        except AttributeError:
            print('ERROR: for class {}'.format(node_class))

        print('')
