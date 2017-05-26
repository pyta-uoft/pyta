import os
# from sys import stdout
import sys

def get_file_paths(rel_path):
    """A generator for iterating python files within a directory.
    `rel_path` is a relative path to a file or directory.
    Returns paths to all files in a directory.
    """
    if not os.path.isdir(rel_path):
        yield rel_path  # Don't do anything; return the file name.
    else:
        for root, _, files in os.walk(rel_path):
            for filename in (f for f in files if f.endswith('.py')):
                yield os.path.join(root, filename)  # Format path, from root.


def get_file_object(output):
    """Reset a file for outputting messages into, and return file object.
    Note: leave the file open during the execution of pyta program 
    because many writes may happen, and the fd should close automatically 
    by the system when the program ends. Default stream to std out.
    Raises IOError.
    """
    if output is None:
        return sys.stdout
    # Use expanduser, for paths that contain system-specific or relative syntax, 
    # e.g. `~`, `../`
    correct_path = os.path.expanduser(output)
    if not os.path.exists(os.path.dirname(correct_path)):
        raise IOError('path {} does not exist.'.format(output))
    if os.path.isdir(correct_path):
        correct_path = os.path.join(correct_path, DEFAULT_OUTPUT_NAME)
    with open(correct_path, 'w') as _:  # erase file, and close it.
        pass
    return open(correct_path, 'a')  # return file object, to append messages to


def filename_to_display(filename):
    """Display the file name, currently consistent with pylint format."""
    return '{} File: {}'.format('*'*15, filename)


def write_stream(string, file_stream):
    """Write output to a certain stream."""
    print(string, file=file_stream)
