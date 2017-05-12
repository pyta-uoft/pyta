"""Python Teaching Assistant

The goal of this module is to provide automated feedback to students in our
introductory Python courses, using static analysis of their code.

To run the checker, call the check function on the name of the module to check.

> import python_ta
> python_ta.check_all('mymodule')

Or, put the following code in your Python module:

if __name__ == '__main__':
    import python_ta
    python_ta.check_all()
"""
import importlib.util
import os
import sys
import tokenize
import webbrowser

import pylint.lint as lint
import pylint.utils as utils
import pylint
from astroid import MANAGER

from .reporters import ColorReporter
from .patches import patch_all

# Local version of website; will be updated later.
HELP_URL = 'http://www.cs.toronto.edu/~david/pyta/'

# Cache the `.pylintrc` absolute path for a given directory absolute path.
# Config files cached in the dict are already loaded into the linter.
_PYLINTRC_CACHE = dict()

# check the python version
if sys.version_info < (3, 4, 0):
    print('You need Python 3.4 or later to run this script')


def check_errors(module_name='', reporter=ColorReporter, number_of_messages=5,
                 config=''):
    """Check a module for errors, printing a report.
    """
    _check(module_name=module_name, reporter=reporter, number_of_messages=number_of_messages, level='error', local_config=config)


def check_all(module_name='', reporter=ColorReporter, number_of_messages=5,
              config=''):
    """Check a module for errors and style warnings, printing a report."""
    _check(module_name, reporter, number_of_messages, level='all',
           local_config=config)


def _find_pylintrc_bottom_up(curr_dir):
    """Search bottom-up for a `.pylintrc` file provided in user location.
    Return absolute path to the file, or None.
    `curr_dir` is an absolute path to a directory, containing a file to check.
    • When run in an IDE (like PyCharm), sys.argv contains the full path,
        - sys.argv[0] is: /<users>/<user>/<path_to>/dir1/dir2/file.py
        - os.getcwd() is: /<users>/<user>/<path_to>/dir1/dir2
    • When run from the Command Line, we need to combine the two,
        - sys.argv[0] is: `dir2/file.py`
        - os.getcwd() is: /<users>/<user>/<path_to>/dir1
    For more info see, pylint.config.find_pylintrc
    """
    found_pylintrc_location = None
    config_was_cached = False
    # Stop searching for `.pylintrc` file ideally at the root of the user
    # codebase, but we don't know where that is without passing extra args.
    # So, at least stop at the user directory, though the file shouldn't be
    # here. It isn't ideal, but its okay for now. Note: this assumes the file
    # will always exist in some location, up the tree.
    stop_at = os.path.expanduser('~')
    while curr_dir != stop_at and found_pylintrc_location is None:
        # Check for curr_dir in the cache first, for efficiency.
        if curr_dir in _PYLINTRC_CACHE:
            found_pylintrc_location = _PYLINTRC_CACHE[curr_dir]
            config_was_cached = True
        # Accept pylintrc as dotfile or not,
        elif os.path.exists(os.path.join(curr_dir, '.pylintrc')):
            found_pylintrc_location = os.path.join(curr_dir, '.pylintrc')
            _PYLINTRC_CACHE[curr_dir] = found_pylintrc_location
        elif os.path.exists(os.path.join(curr_dir, 'pylintrc')):
            found_pylintrc_location = os.path.join(curr_path, 'pylintrc')
            _PYLINTRC_CACHE[curr_dir] = found_pylintrc_location
        curr_dir = os.path.abspath(os.path.join(curr_dir, '..'))  # parent dir
    return found_pylintrc_location, config_was_cached


def _load_pylint_plugins(current_reporter, local_config, pep8):
    """Register checker plugins for pylint. Return linter."""
    linter = lint.PyLinter(reporter=current_reporter)
    linter.load_default_plugins()
    linter.load_plugin_modules(['python_ta/checkers/forbidden_import_checker',
                                'python_ta/checkers/global_variables_checker',
                                'python_ta/checkers/dynamic_execution_checker',
                                'python_ta/checkers/IO_Function_checker',
                                # TODO: Fix this test
                                #'python_ta/checkers/invalid_range_index_checker',
                                'python_ta/checkers/assigning_to_self_checker',
                                'python_ta/checkers/always_returning_checker',
                                'python_ta/checkers/type_inference_checker'])
    if pep8:
        linter.load_plugin_modules(['python_ta/checkers/pycodestyle_checker'])

    if isinstance(local_config, str) and local_config != '':
        # Use config file at the specified path instead of the default.
        linter.read_config_file(local_config)
    else:
        # Start at the origin (file) of the call to the `check` function.
        if sys.argv[0].startswith(os.getcwd()):
            curr_path = os.path.dirname(sys.argv[0])
        else:
            curr_path = os.path.dirname(os.path.join(os.getcwd(), sys.argv[0]))

        pylintrc_location, _ = _find_pylintrc_bottom_up(curr_path)
        if pylintrc_location is not None:
            # Use config file in user 's codebase location.
            linter.read_config_file(pylintrc_location)
        else:
            # Use default config file in the python_ta package.
            linter.read_config_file(os.path.join(os.path.dirname(__file__), '.pylintrc'))

        # Override part of the default config, with a dict of config options.
        if isinstance(local_config, dict):
            for key in local_config:
                linter.global_set_option(key, local_config[key])

    linter.load_config_file()
    return linter


def _apply_nearest_config(linter=None, file_abs_path=''):
    """Apply the nearest `.pylintrc` config file (options) to files that are
    linted in a recursive call to _check.
    """
    curr_dir = file_abs_path
    if file_abs_path.endswith('.py'):
        curr_dir = os.path.dirname(file_abs_path)
    pylintrc_location, config_was_cached = _find_pylintrc_bottom_up(curr_dir)
    if not config_was_cached:
        linter.read_config_file(pylintrc_location)
        linter.load_config_file()


def _verify_pre_check(filepath):
    """Check student code for certain issues."""

    # Make sure the program doesn't crash for students.
    # Could use some improvement for better logging and error reporting.
    try:
        # Check for inline "pylint:" comment, which may indicate a student
        # trying to disable a check.
        with tokenize.open(filepath) as f:
            for (tok_type, content, _, _, _) in tokenize.generate_tokens(f.readline):
                if tok_type != tokenize.COMMENT:
                    continue
                match = pylint.utils.OPTION_RGX.search(content)
                if match is not None:
                    print('ERROR: string "pylint:" found in comment. ' +
                          'No check run on file `{}`\n'.format(filepath))
                    return False
    except IndentationError as e:
        print('ERROR: python_ta could not check your code due to an ' +
              'indentation error at line {}'.format(e.lineno))
        return False
    except tokenize.TokenError as e:
        print('ERROR: python_ta could not check your code due to a ' +
              'syntax error in your file')
        return False
    return True


def _check(module_name='', reporter=ColorReporter, number_of_messages=5, level='all',
           local_config='', pep8=False):
    """Check a module for problems, printing a report.

    The `module_name` can take several inputs:
    - a string of the directory, or file to check (`.py` extension is optional). 
    - a list of strings of directories or files.
    - or not provided, to check the current python file.

    `level` is used to specify which checks should be made.

    `local_config` is a dict of config options, or string of a config file name.
    """
    valid_module_names = []

    # Allow call to check with empty args
    if module_name == '':
        m = sys.modules['__main__']
        spec = importlib.util.spec_from_file_location(m.__name__, m.__file__)
        module_name = [spec.origin]
    # Enforce API to expect 1 file or directory if type is list
    elif isinstance(module_name, str):
        module_name = [module_name]
    # otherwise, enforce API to expect `module_name` type as list
    elif not isinstance(module_name, list):
        print('No checks run. Input to check, `{}`, has invalid type, must be a list of strings.\n'.format(module_name))
        return

    current_reporter = reporter(number_of_messages)
    linter = _load_pylint_plugins(current_reporter, local_config, pep8)
    
    patch_all()  # Monkeypatch pylint

    for item in module_name:
        if not isinstance(item, str):  # Issue errors for invalid types
            current_reporter.show_file_linted(item)
            print('No check run on file `{}`, with invalid type. Must be type: str.\n'.format(item))
        else:  # Check other valid files.
            valid_module_names.append(item)

    try:
        expanded_files, errors = utils.expand_modules(valid_module_names, 
                        linter.config.black_list, linter.config.black_list_re)
        for error in errors:
            current_reporter.show_file_linted(error['mod'])
            if isinstance(error['ex'], ImportError):
                print('Error: {}, which means the file "{}" could not be found.\n'
                      .format(error['ex'], error['mod']))
            else:
                print('Error: {}\n'.format(error['ex']))

        for descr in expanded_files:
            modname, filepath, is_arg = descr['name'], descr['path'], descr['isarg']
            # Load config file, where applicable (e.g. recursively check a dir)
            _apply_nearest_config(linter, os.path.abspath(filepath))
            current_reporter.show_file_linted(modname)
            if not _verify_pre_check(filepath):
                continue  # Check the other files
            linter.check(filepath)  # Lint !
            current_reporter.print_messages(level)
            current_reporter.reset_messages()  # Clear lists for any next file.

    except Exception as e:
        print('Unexpected error encountered - please report this to david@cs.toronto.edu!')
        print('Error message: "{}"'.format(e))
        raise e


def doc(msg_id):
    """Open a webpage explaining the error for the given message."""
    msg_url = HELP_URL + '#' + msg_id
    print('Opening {} in a browser.'.format(msg_url))
    webbrowser.open(msg_url)
