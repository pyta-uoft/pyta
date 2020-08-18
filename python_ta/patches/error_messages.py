"""Patch pylint error messages."""
from importlib import import_module

# global
patch_data = {
    'pylint.checkers.base': {
        'BasicChecker': {
            'E0111': 'reversed() can only be called on sequence types. This '
                     'typically occurs because you\'re trying to reverse '
                     'something that isn\'t a str, list, or tuple.',
            'W0101': 'Code after a return or raise statement will '
                     'never be run, so either the function is '
                     'returning early or you should remove it.',
            'W0102': 'Dangerous default value %s as argument. '
                     'Using mutable values as a default argument '
                     'is a common cause of confusing and unwanted behaviour.',
            'W0104': 'This statement doesn\'t have any effect, and could be '
                     'removed without changing the behaviour of the program.',
            'W0106': 'Right now, expression %s isn\'t being used by the rest '
                     'of your code. You should either remove this expression or '
                     'save it in a variable to use it later.',
            'W0108': 'This lambda function isn\'t necessary since you can pass '
                     'the arguments directly to the function you\'re calling in '
                     'the lambda\'s body.',
            'W0109': 'Duplicate key %r in dictionary. '
                     'When constructing a dictionary, the last value assigned '
                     'to a key takes precedence, making previous ones redundant.',
            'W0122': 'Using `exec()` to evaluate a code-block represented as a '
                     'str can be potentially dangerous, and is typically a sign of poor design.',
            'W0123': 'Using `eval()` to evaluate an expression represented as a '
                     'str can be potentially dangerous, and is typically a sign of poor design.',
            'W0199': 'Calling assert on a tuple will only evaluate to false if '
                     'it is empty. It\'s likely you intended \'assert x, y\' rather '
                     'than \'assert (x,y)\'.'
        },
        'ComparisonChecker': {
            'R0123': 'The \'is\' operator compares the ids of its two arguments, not '
                     'their values. When performing comparison with a literal, '
                     'this is usually not what you want. Did you mean \'==\'?',
            'C0123': 'You should use \'isinstance\' rather than \'type\' to '
                     'check the type of a value.'
        },
        'NameChecker': {
            'C0102': 'Black listed name "%s". You should give your variables '
                     'meaningful rather than generic names.',
            'C0103': '%s name "%s" doesn\'t conform to %s. '
                     'Please refer to the PyTA Help Documentation for more information '
                     'on Python Naming Conventions.'
        },
        'PassChecker': {
            'W0107': 'Unnecessary pass statement (you should remove this). '
                     'A pass statement should only be used to represent '
                     'an \"empty\" code block, where nothing happens.'
        },
        'BasicErrorChecker': {
            'E0101': '__init__ is called only to initialize the attributes of a new object. '
                     'It should not return anything.',
            'E0102': '%s was already defined line %s. '
                     'You should make sure all functions, methods and classes '
                     'defined have different names.',
            'E0103': 'The %r keyword should only be used inside a loop.',
            'E0104': 'The \'return\' keyword is used to end the execution of a function '
                     'and return a result, so you should only use it inside of a function.',
            'E0108': 'Duplicate parameter name %s in function definition. '
        }
    },
    'pylint.checkers.refactoring': {
        'RefactoringChecker': {
            'R1710': 'Since this function can return a non-None value, you should '
                     'explicitly write "return None" whenever None is returned by '
                     'this function. (Possibly including at the end of the function body.)'
        }
    },
    'pylint.checkers.design_analysis': {
        'MisdesignChecker': {
            'R0912': 'This function has too many branches (%s, exceeding limit %s). '
                     'You should try to reduce the complexity of the function '
                     'by splitting it up into helper functions.',
            'R0913': 'This function has too many parameters (%s, exceeding limit %s). '
                     'You should try to reduce the complexity of the function '
                     'by splitting up it, or combining related objects as a single one.',
            'R0914': 'This function has too many local variables (%s, exceeding limit %s). '
                     'You should try to reduce the complexity of the function '
                     'by splitting up it, or combining related objects as a single one.',
            'R0915': 'This function has too many statements ((%s, exceeding limit %s). '
                     'It should be split up into smaller functions.',
            'R0916': 'This if statement contains too many boolean expressions '
                     '(%s, exceeding limit %s). You should see if you can reduce '
                     'the amount of expressions, or split it into branches.',
        }
    },
    'pylint.checkers.classes': {
        'ClassChecker': {
            'E0203': 'You can\'t use instance attribute %r prior to its assignment '
                     'on line %s.',
            'E0211': 'Every instance method requires at least one parameter, since the '
                     'first parameter refers to the object on which this method is called. '
                     'Python\'s convention is to name this parameter \'self\'.',
             'E0213': 'The first parameter of a method should always be called \'self\'. '
                      'Even though this isn\'t technically required, it is a strong convention '
                      'used by all Python programmers.',
             'E0241': 'This class %r should not inherit from the same class multiple times.',
             'R0201': 'This method does not make use of \'self\', so you should remove the self '
                      'parameter and move this method outside of the class (turning it into a '
                      'top-level function.',
             'R0205': 'Class %r inherits from \'object\'. '
                      'All classes inherit from object by default, so you do not need to specify '
                      'this in the class header.',
             'W0211': 'The static method %r contains \'self\' as the first parameter. '
                      'Static methods shouldn\'t have this, since this suggests we are expecting '
                      'a class instance as the first argument.',
             'W0212': 'Since %s starts with an underscore, it should be considered '
                      '"private", and not accessed outside of the class in which it is defined.',
             'W0221': 'This method must take the same number of arguments as %s %r method.',
             'W0222': 'This method\'s parameters must have the same name, order, and default '
                      'arguments as %s %r method.',
             'W0223': 'The abstract method %r in class %r must be overridden within a '
                      'concrete subclass.',
             'W0231': 'Subclass \'__init__\' method should call the \'__init__\' method from '
                      'it\'s base class %r.',
             'W0233': 'Subclass \'__init__\' method should call the \'__init__\' method of '
                      'the parent class rather than some unrelated class %r.',
        },
        'SpecialMethodsChecker': {
            'E0302': 'The special method %r expects to take %s parameters, but %d %s given.',
        },
    },
    'pylint.checkers.exceptions': {
        'ExceptionsChecker': {
            'E0701': '\'except\' blocks are checked top to bottom, so generic exception types should '
                     'come after specific exception types. Otherwise, the block for the specific '
                     'exception type will never be reached. (%s)',
            'E0702': '\'raise\' is used to raise exceptions. Anything else will lead to an error. '
                     '(Raising %s)',
            'E0704': 'This \'raise\' statement must have an exception class or instance.',
            'E0710': 'This \'raise\' statement is using a class that is not a subclass of Exception.',
            'E0711': 'You mean to raise \'NotImplementedError\', which indicates that the abstract method '
                     'must be implemented by the derived class. \'NotImplemented\' is strictly used as a '
                     'return value for binary special methods (e.g __eq__), indicating that they\'re not implemented.',
            'E0712': '\'except\' expects a class that is a subclass of the Exception class (%s is not).',
            'W0702': 'It\'s bad practice to use the \'except\' keyword without passing an exception, '
                     'since any and all expressions will be caught, which may lead to undetected errors '
                     'in your code.',
            'W0703': 'It\'s bad practice to use \'except: %s\' since any and all expressions '
                     'will be caught, which may lead to undetected errors in your code.',
            'W0705': '\'except\' blocks are checked top to bottom, so if we try to catch the same '
                     'exception %s multiple times, only the first \'except\' block for the exception '
                     'will be reached.',
            'W0706': 'If the \'except\' block uses \'raise\' as its first or only operator, it '
                     'will just raise back the exception immediately.',
            'W0711': '\'except\' can handle multiple exceptions, but they have to be written as a '
                     'tuple. For example, use \'except (A, B)\' instead of \'except A %s B\'',
            'W0716': 'This is not a valid operation on exceptions. %s'
        }
    },
    'pylint.checkers.format': {
        'FormatChecker': {
            'W0301': 'You should remove this semicolon. In Python, statements are separated by '
                     'starting each one on a new line.',
            'W0312': 'This code is indented with both %ss and %ss. You should use spaces to indent your code.',
            'C0301': 'This line is %s characters long, exceeding the limit of %s characters.',
            'C0303': 'Trailing whitespace is poor formatting, and should be removed.',
            'C0304': 'By convention, each Python file should end with a blank line. To fix this, '
                     'go down to the bottom of your file and press Enter/Return to add an empty line.',
            'C0321': 'Writing multiple statements on a single line makes your code harder to read and '
                     'understand, and should be avoided.',
            'C0330': 'Wrong %s indentation%s%s.\n%s%s. This error occured because of an '
                     'inconsistent use of number of spaces for indentation.'
        }
    },
    'pylint.checkers.imports': {
        'ImportsChecker': {
            'E0401': 'Unable to import %s. Check the spelling of the module name, or '
                     'whether the module is installed (if it is a module you did not write), '
                     'or whether the module is in the same directory as this file '
                     '(if it is a module you did write).',
            'W0401': 'Wildcard (*) imports add all objects from the imported module as '
                     'global variables, which may result in name collisions. You should only '
                     'import from %s what you need, or import the whole module '
                     '("import module") and use dot notation to access the module\'s functions/classes.',
            'W0404': 'Module %r was reimported on line %s. A module should not be '
                     'imported more than once.',
            'W0410': 'Imports of \'__future__\' must be the first non-docstring statement in the module.',
            'C0410': 'Different modules should not be imported on a single line. You '
                     'should import each module on line %s on separate lines.',
            'C0414': 'The \'import as\' is used to import a module and give it a different name in this file. '
                     'If you don\'t want to rename the module, simply use \'import\' instead.'
        }
    },
    'pylint.checkers.misc': {
        'EncodingChecker': {
            'W0511': 'The warning %s was found.'
        }
    },
    'pylint.checkers.newstyle': {
        'NewStyleConflictChecker': {
            'E1003': 'The first argument to \'super\' should be the current class. '
                     'The argument %r is not valid.'
        }
    }
}


# We are assuming only the first elements of the tuple values in <msgs> are being patched.
def patch_error_messages():
    """Patch <msgs> in pylint checkers to make them more helpful for python_ta clients."""
    for file_name, file_data in patch_data.items():
        for checker_name, checker_data in file_data.items():
            # only access the specific variable being changed
            checker = getattr(import_module(file_name), checker_name)
            if hasattr(checker, 'msgs'):
                for error_id, new_msg in checker_data.items():
                    lst_msg = list(checker.msgs[error_id])
                    # first element of the tuple value changed
                    lst_msg[0] = new_msg
                    checker.msgs[error_id] = tuple(lst_msg)
            else:
                print('no msgs attribute!')
