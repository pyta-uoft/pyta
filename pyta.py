"""Python Teaching Assistant

The goal of this module is to provide automated feedback to students in our
introductory Python courses, using static analysis of their code.

To run the checker, call the check function on the name of the module to check.

> import pyta
> pyta.check_all('mymodule')
"""
import importlib.util
import pylint.lint as lint
from reporters.color_reporter import PlainReporter
from astroid import MANAGER

import webbrowser
import sys
import os

# Local version of website; will be updated later.
HELP_URL = 'http://www.cs.toronto.edu/~david/pyta/'


# Checks to enable for basic_check (trying to find errors
# and forbidden constructs only)
BASIC_CHECKS = [
    'used-before-assignment',
    'undefined-variable',
    'undefined-loop-variable',
    'not-in-loop',
    'return-outside-function',
    'duplicate-key',
    'unreachable',
    'pointless-statement',
    'pointless-string-statement'
    'no-member',
    'not-callable',
    'assignment-from-no-return',
    'assignment-from-none',
    'no-value-for-parameter',
    'too-many-function-args',
    'invalid-sequence-index',
    'invalid-slice-index',
    'invalid-unary-operand-type',
    'unsupported-binary-operation',
    'unsupported-membership-test',
    'unsubscriptable-object',
    'unbalanced-tuple-unpacking',
    'unpacking-non-sequence',
    'function-redefined',
    'duplicate-argument-name',
    'import-error',
    'no-name-in-module',
    'non-parent-init-called',
    'access-member-before-definition',
    'method-hidden',
    'unexpected-special-method-signature',
    'inherit-non-class',
    'duplicate-except',
    'bad-except-order',
    'raising-bad-type',
    'raising-non-exception',
    'catching-non-exception',
    'E9996',
    'E9991',
    'E0001',
    'E9999'
]


# check the python version
if sys.version_info < (3, 4, 0):
    print('You need Python 3.4 or later to run this script')


def check_basic(module_name, reporter=PlainReporter, number_of_messages=5):
    """Check a module for errors, printing a report.

    The name of the module should be passed in as a string,
    without a file extension (.py).
    """
    # Check if `module_name` is not the type str, raise error.
    if not isinstance(module_name, str):
        print("The Module '{}' has an invalid name. Module name must be the "
              "type str.".format(module_name))
        return

    module_name = module_name.replace(os.path.sep, '.')

    # Detect if the extension .py is added, and if it is, remove it.
    if module_name.endswith('.py'):
        module_name = module_name[:-3]

    # Reset astroid cache
    MANAGER.astroid_cache.clear()

    spec = importlib.util.find_spec(module_name)

    current_reporter = reporter(number_of_messages)
    linter = lint.PyLinter(reporter=current_reporter)
    linter.load_default_plugins()
    linter.load_plugin_modules(['checkers/forbidden_import_checker',
                                'checkers/global_variables_checker',
                                'checkers/dynamic_execution_checker',
                                'checkers/IO_Function_checker',
                                # TODO: Fix this test
                                #'checkers/invalid_range_index_checker',
                                'checkers/assigning_to_self_checker',
                                'checkers/always_returning_checker'])
    linter.read_config_file()
    linter.load_config_file()

    linter.global_set_option('disable', 'all')
    linter.global_set_option('enable',
                             BASIC_CHECKS)

    # When module is not found, raise exception.
    try:
        linter.check([spec.origin])
    except AttributeError:
        print("The Module '{}' could not be found. ".format(module_name))
        return
    except Exception as e:
        print('Unexpected error encountered - please report this to david@cs.toronto.edu!')
        print(e)

    current_reporter.print_message_ids()


def check_all(module_name, reporter=PlainReporter, number_of_messages=5):
    """Check a module for errors, printing a report.

    The name of the module should be passed in as a string,
    without a file extension (.py).
    """
    # Check if `module_name` is not the type str, raise error.
    if not isinstance(module_name, str):
        print("The Module '{}' has an invalid name. Module name must be the "
              "type str.".format(module_name))
        return

    module_name = module_name.replace(os.path.sep, '.')

    # Detect if the extension .py is added, and if it is, remove it.
    if module_name.endswith('.py'):
        module_name = module_name[:-3]

    # Reset astroid cache
    MANAGER.astroid_cache.clear()

    spec = importlib.util.find_spec(module_name)

    current_reporter = reporter(number_of_messages)
    linter = lint.PyLinter(reporter=current_reporter)
    linter.load_default_plugins()
    linter.load_plugin_modules(['checkers/forbidden_import_checker',
                                'checkers/global_variables_checker',
                                'checkers/dynamic_execution_checker',
                                'checkers/IO_Function_checker',
                                # TODO: Fix this test
                                #'checkers/invalid_range_index_checker',
                                'checkers/assigning_to_self_checker',
                                'checkers/always_returning_checker'])
    linter.read_config_file()
    linter.load_config_file()

    # When module is not found, raise exception.
    try:
        linter.check([spec.origin])
    except AttributeError:
        print("The Module '{}' could not be found. ".format(module_name))
        return
    except Exception as e:
        print('Unexpected error encountered - please report this to david@cs.toronto.edu!')
        print(e)

    current_reporter.print_message_ids()


def doc(msg_id):
    """Open a webpage explaining the error for the given message."""
    msg_url = HELP_URL + '#' + msg_id
    print('Opening {} in a browser.'.format(msg_url))
    webbrowser.open(msg_url)
