"""Python Teaching Assistant

The goal of this module is to provide automated feedback to students in our
introductory Python courses, using static analysis of their code.

To run the checker, call the check function on the name of the module to check.

> import python_ta
> python_ta.check_all('mymodule.py')

Or, put the following code in your Python module:

if __name__ == '__main__':
    import python_ta
    python_ta.check_all()
"""
__version__ = "1.8.0a1"  # Version number

# First, remove underscore from builtins if it has been bound in the REPL.
import builtins
try:
    del builtins._
except AttributeError:
    pass

import importlib.util
import os
import sys
import tokenize
from typing import Generator
import webbrowser

import pylint.lint
import pylint.utils
from pylint.utils.pragma_parser import OPTION_PO

from astroid import modutils, MANAGER

from .reporters import REPORTERS
from .patches import patch_all
from .upload import upload_to_server


HELP_URL = 'http://www.cs.toronto.edu/~david/pyta/'

# check the python version
if sys.version_info < (3, 7, 0):
    print('[WARNING] You need Python 3.7 or later to run PythonTA.')


# Flag to determine if we've previously patched pylint
PYLINT_PATCHED = False


def check_errors(module_name='', config='', output=None):
    """Check a module for errors, printing a report."""
    return _check(module_name=module_name, level='error', local_config=config,
                  output=output)


def check_all(module_name='', config='', output=None):
    """Check a module for errors and style warnings, printing a report."""
    return _check(module_name=module_name, level='all', local_config=config,
                  output=output)


def _check(module_name='', level='all', local_config='', output=None):
    """Check a module for problems, printing a report.

    The `module_name` can take several inputs:
      - string of a directory, or file to check (`.py` extension optional).
      - list of strings of directories or files -- can have multiple.
      - no argument -- checks the python file containing the function call.
    `level` is used to specify which checks should be made.
    `local_config` is a dict of config options or string (config file name).
    `output` is an absolute or relative path to capture pyta data output. Default std out.
    """
    linter = reset_linter(config=local_config)
    current_reporter = linter.reporter
    current_reporter.set_output(output)

    global PYLINT_PATCHED
    if not PYLINT_PATCHED:
        patch_all()  # Monkeypatch pylint (override certain methods)
        PYLINT_PATCHED = True

    # Try to check file, issue error message for invalid files.
    try:
        for locations in _get_valid_files_to_check(module_name):
            f_paths = []  # Paths to files for data submission
            errs = []  # Errors caught in files for data submission
            config = {}  # Configuration settings for data submission
            for file_py in get_file_paths(locations):
                if not _verify_pre_check(file_py):
                    continue  # Check the other files
                # Load config file in user location. Construct new linter each
                # time, so config options don't bleed to unintended files.
                # Reuse the same reporter each time to accumulate the results across different files.
                linter = reset_linter(config=local_config, file_linted=file_py)
                linter.set_reporter(current_reporter)
                module_name = os.path.splitext(os.path.basename(file_py))[0]
                if module_name in MANAGER.astroid_cache:  # Remove module from astroid cache
                    del MANAGER.astroid_cache[module_name]
                linter.check(file_py)  # Lint !
                current_reporter.print_messages(level)
                if linter.config.pyta_file_permission:
                    f_paths.append(file_py)  # Appending paths for upload
                print('[INFO] File: {} was checked using the configuration file: {}'.format(
                    file_py, linter.config_file), file=sys.stderr)
            if linter.config.pyta_error_permission:
                errs = list(current_reporter.messages.values())
            if f_paths != [] or errs != []:  # Only call upload_to_server() if there's something to upload
                # Checks if default configuration was used without changing options through the local_config argument
                if linter.config_file[-19:-10] != "python_ta" or local_config != '':
                    config = linter.config.__dict__
                upload_to_server(errors=errs,
                                 paths=f_paths,
                                 config=config,
                                 url=linter.config.pyta_server_address,
                                 version=__version__)
        linter.generate_reports()
        return current_reporter
    except Exception as e:
        print('[ERROR] Unexpected error encountered! Please report this to your instructor (and attach the code that caused the error).')
        print('[ERROR] Error message: "{}"'.format(e))
        raise e


def _find_local_config(curr_dir):
    """Search for a `.pylintrc` configuration file provided in same (user)
    location as the source file to check.
    Return absolute path to the file, or None.
    `curr_dir` is an absolute path to a directory, containing a file to check.
    For more info see, pylint.config.find_pylintrc
    """
    if curr_dir.endswith('.py'):
        curr_dir = os.path.dirname(curr_dir)
    if os.path.exists(os.path.join(curr_dir, '.pylintrc')):
        return os.path.join(curr_dir, '.pylintrc')
    elif os.path.exists(os.path.join(curr_dir, 'pylintrc')):
        return os.path.join(curr_dir, 'pylintrc')


def _load_config(linter, config_location):
    """Load configuration into the linter."""
    linter.read_config_file(config_location)
    linter.config_file = config_location
    linter.load_config_file()


def reset_linter(config=None, file_linted=None):
    """Construct a new linter. Register config and checker plugins.

    To determine which configuration to use:
    - If the config argument is a string, use the config found at that location,
    - Otherwise,
        - Try to use the config file at directory of the file being linted,
        - Otherwise try to use default config file shipped with python_ta.
        - If the config argument is a dictionary, apply those options afterward.
    Do not re-use a linter object. Returns a new linter.
    """
    # Tuple of custom options. Note: 'type' must map to a value equal a key in the pylint/config/option.py `VALIDATORS` dict.
    new_checker_options = (
        ('pyta-type-check',
            {'default': False,
             'type': 'yn',
             'metavar': '<yn>',
             'help': 'Enable the type-checker.'}),
        ('pyta-number-of-messages',
            {'default': 5,
             'type': 'int',
             'metavar': '<number_messages>',
             'help': 'Display a certain number of messages to the user, without overwhelming them.'}),
        ('pyta-template-file',
            {'default': 'template.html',
             'type': 'string',
             'metavar': '<pyta_reporter>',
             'help': 'Template file for html format of htmlreporter output.'}),
        ('pyta-error-permission',
         {'default': False,
          'type': 'yn',
          'metavar': '<yn>',
          'help': 'Permission to anonymously submit errors'}),
        ('pyta-file-permission',
         {'default': False,
          'type': 'yn',
          'metavar': '<yn>',
          'help': 'Permission to anonymously submit files and errors'}),
        ('pyta-server-address',
         {'default': 'http://127.0.0.1:5000',
          'type': 'string',
          'metavar': '<server-url>',
          'help': 'Server address to submit anonymous data'})
    )

    custom_checkers = [
        'python_ta.checkers.forbidden_import_checker',
        'python_ta.checkers.possibly_undefined_checker',
        'python_ta.checkers.global_variables_checker',
        'python_ta.checkers.forbidden_io_function_checker',
        'python_ta.checkers.invalid_range_index_checker',
        'python_ta.checkers.one_iteration_checker',
        'python_ta.checkers.type_annotation_checker',
        'python_ta.checkers.unnecessary_indexing_checker',
        'python_ta.checkers.shadowing_in_comprehension_checker',
        'python_ta.checkers.redundant_assignment_checker',
        'python_ta.checkers.invalid_for_target_checker',
        'python_ta.checkers.missing_space_in_doctest_checker',
        'python_ta.checkers.pycodestyle_checker'
    ]

    # Register new options to a checker here to allow references to
    # options in `.pylintrc` config file.
    # Options stored in linter: `linter._all_options`, `linter._external_opts`
    linter = pylint.lint.PyLinter(options=new_checker_options)
    linter.load_default_plugins()  # Load checkers, reporters
    linter.load_plugin_modules(custom_checkers)

    if isinstance(config, str) and config != '':
        # Use config file at the specified path instead of the default.
        _load_config(linter, config)
    else:
        # If available, use config file at directory of the file being linted.
        pylintrc_location = None
        if file_linted:
            pylintrc_location = _find_local_config(file_linted)

        # Otherwise, use default config file shipped with python_ta package.
        if not pylintrc_location:
            pylintrc_location = _find_local_config(os.path.dirname(__file__))

        _load_config(linter, pylintrc_location)

        # Override part of the default config, with a dict of config options.
        # Note: these configs are overridden by config file in user's codebase
        # location.
        if isinstance(config, dict):
            for key in config:
                linter.global_set_option(key, config[key])

    # Custom checker configuration.
    if linter.config.pyta_type_check:
        linter.load_plugin_modules(['python_ta.checkers.type_inference_checker'])

    return linter


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


def _verify_pre_check(filepath):
    """Check student code for certain issues."""
    # Make sure the program doesn't crash for students.
    # Could use some improvement for better logging and error reporting.
    try:
        # Check for inline "pylint:" comment, which may indicate a student
        # trying to disable a check.
        with tokenize.open(os.path.expanduser(filepath)) as f:
            for tok_type, content, _, _, _ in tokenize.generate_tokens(f.readline):
                if tok_type != tokenize.COMMENT:
                    continue
                match = OPTION_PO.search(content)
                if match is not None:
                    print('[ERROR] String "pylint:" found in comment. ' +
                          'No check run on file `{}.`\n'.format(filepath))
                    return False
    except IndentationError as e:
        print('[ERROR] python_ta could not check your code due to an ' +
              'indentation error at line {}.'.format(e.lineno))
        return False
    except tokenize.TokenError as e:
        print('[ERROR] python_ta could not check your code due to a ' +
              'syntax error in your file.')
        return False
    except UnicodeDecodeError:
        print('[ERROR] python_ta could not check your code due to an ' +
              'invalid character. Please check the following lines '
              'in your file and all characters that are marked with a �.')
        with open(os.path.expanduser(filepath), encoding='utf-8', errors='replace') as f:
            for i, line in enumerate(f):
                if '�' in line:
                    print(f'  Line {i}: {line}', end='')
        return False
    return True


def _get_valid_files_to_check(module_name: str) -> Generator[str, None, None]:
    """A generator for all valid files to check.
    """
    # Allow call to check with empty args
    if module_name == '':
        m = sys.modules['__main__']
        spec = importlib.util.spec_from_file_location(m.__name__, m.__file__)
        module_name = [spec.origin]
    # Enforce API to expect 1 file or directory if type is list
    elif isinstance(module_name, str):
        module_name = [module_name]
    # Otherwise, enforce API to expect `module_name` type as list
    elif not isinstance(module_name, list):
        print('No checks run. Input to check, `{}`, has invalid type, must be a list of strings.'.format(module_name))
        return

    # Filter valid files to check
    for item in module_name:
        if not isinstance(item, str):  # Issue errors for invalid types
            print('No check run on file `{}`, with invalid type. Must be type: str.\n'.format(item))
        elif os.path.isdir(item):
            yield item
        elif not os.path.exists(os.path.expanduser(item)):
            try:
                # For files with dot notation, e.g., `examples.<filename>`
                filepath = modutils.file_from_modpath(item.split('.'))
                if os.path.exists(filepath):
                    yield filepath
                else:
                    print('Could not find the file called, `{}`\n'.format(item))
            except ImportError:
                print('Could not find the file called, `{}`\n'.format(item))
        else:
            yield item  # Check other valid files.


def doc(msg_id):
    """Open a webpage explaining the error for the given message."""
    msg_url = HELP_URL + '#' + msg_id
    print('Opening {} in a browser.'.format(msg_url))
    webbrowser.open(msg_url)
