"""Patch pylint error messages."""
from importlib import import_module

# global
patch_data = {
    'pylint.checkers.base': {
        'BasicChecker':
            {'E0111': 'reversed() can only be called on sequence types. This '
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
             'W0106': 'Expression "%s" isn\'t assigned to a variable.',
             'W0108': 'The lambda function isn\'t necessary since the lambda '
                      'arguments are only being passed into a function call.',
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
        'ComparisonChecker':
            {'R0123': 'tHE \'is\' keyword compares two objects location in memory rather '
                      'than value equality. When performing comparison with a literal, '
                      'this is usually not what you want. Did you mean \'==\'?',
             'C0123': 'You should use \'isinstance\' rather than \'type\' to '
                      'perform a typecheck.'
             },
        'NameChecker':
            {'C0102': 'Black listed name "%s". You should give your variables '
                      'meaningful rather than generic names.',
             'C0103': '%s name "%s" doesn\'t conform to %s. '
                      'Please refer to the PyTA Help Documentation for more information '
                      'on Python Naming Conventions.'
             },
        'PassChecker':
            {'W0107': 'Unnecessary pass statement (you should remove this). '
                      'A pass statement should only be used to represent '
                      'an \"empty\" code block, where nothing happens.'},
        'BasicErrorChecker':
            {'E0101': '__init__ is called by the special method __new__ '
                      'when a new object is instantiated, and will raise '
                      'a TypeError if __init__ returns anything other than None.',
             'E0102': '%s already defined line %s. '
                      'You should make sure all functions, methods and classes '
                      'defined have different names.',
             'E0103': 'The %r keyword should only be used inside a loop.',
             'E0104': 'The \'return\' keyword is used to end the execution of a function '
                      'and return a result, so you should only use it inside of a function. '
                      'Note that if no return statement is written, Python implicitly '
                      'ends the execution of a function with return None',
             'E0108': 'Duplicate parameter name %s in function definition. '
             }
    },
    'pylint.checkers.refactoring': {
        'RefactoringChecker':
            {'R1710': 'Since this function can return a non-None value, you should '
                      'explicitly write "return None" whenever None is returned by '
                      'this function. (Possibly including at the end of the function body.)'
             }
    },
    'pylint.checkers.design_analysis': {
        'MisdesignChecker': {'R0912': 'The function has too many branches (%s out of a default limit '
                                      'of %s). You should try to reduce the complexity of the function '
                                      'by splitting it up.',
                             'R0913': 'The function has too many parameters (%s out of a default limit '
                                      'of %s). You should try to reduce the complexity of the function '
                                      'by splitting up it, or combining related objects as a single one.',
                             'R0914': 'The function has too many local variables (%s out of a default limit '
                                      'of /%s).',
                             'R0915': 'The function or method has too many statements (%s out of a default limit '
                                      'of /%s). It should be split up into smaller functions or methods.',
                             'R0916': 'The if statement contains too many boolean expressions '
                                      '(%s out of a default limit of %s). You should see if you can reduce '
                                      'the amount of expressions, or split it into branches.',
                             }
    },
    'pylint.checkers.classes': {
        'ClassChecker': {'E0203': 'You can\'t use class member %r prior to it\'s assignment '
                                  'on line %s.',
                         'E0211': 'Every class method requires at least one parameter, '
                                  'which we conventionally name \'self\'.',
                         'E0213': 'The first parameter of a method should always be called \'self\'. '
                                  'This is a strongly adhered to convention.',
                         'E0241': 'The class %r should not inherit from the same class multiple times.',
                         'R0201': 'Method does not make use of \'self\', so you should rewrite the '
                                  'method as a function and move it outside the class.',
                         'R0205': 'Class %r inherits from \'object\', which can be omitted in Python3.',
                         'W0211': 'Static method %r shouldn\'t contain \'self\' as the first parameter, '
                                  'since this suggests we are expecting a class instance as the first argument.',
                         'W0212': 'Since %s starts with an underscore, it should be considered '
                                  '"private", and not accessed outside of the class in which it is '
                                  'defined.',
                         'W0221': 'Method must take the same number of arguments as %s %r method.',
                         'W0222': 'The method parameters must have the same name, order, and default '
                                  'arguments as %s %r method.',
                         'W0233': 'The abstract method %r in class %r must be overridden within a '
                                  'concrete class.',
                         'W0231': 'Child class should call the \'__init__\' method from it\'s base class %r.',
                         'W0233': 'Child class should call the \'__init__\' method of the parent class '
                                  'rather than some unrelated class.',
                         },
        'SpecialMethodsChecker': {
            'E0302': 'The special method %r expects to take %s parameters, but %d %s given.',
        },
    },
    'pylint.checkers.exceptions': {
        'ExceptionsChecker': {
            'E0701': '\'except\' blocks are analyzed top to bottom, so generic exception types should '
                     'come after specific exception types. Otherwise, the block for the specific '
                     'exception type will never be reached. (%s)',
            'E0702': '\'raise\' is used to raise Exceptions. Anything else will lead to an error. '
                     '(Raising %s)',
            'E0704': '\'raise\' may only be called without an expression inside an \'except\' block.',
            'E0710': '\'raise\' expects an object derived from the BaseException class. Attempting to '
                     'raise any other object will lead to an error.',
            'E0711': '\'NotImplemented\' is strictly used as a return value for binary special methods '
                     '(e.g __eq__), indicating that they\'re not implemented. You mean to raise '
                     '\'NotImplementedError\', which indicates that the abstract method must be '
                     'implemented by the derived class.',
            'E0712': '\'except\' expects an object derived from the BaseException class. Attempting to '
                     'raise any other object will lead to an error.',
            'W0702': 'It\'s bad practice to use the \'except\' keyword without passing an expression, '
                     'since any and all expressions will be caught, which may lead to bugs.',
            'W0703': 'It\'s bad practice to use \'except: Exception\' since any and all expressions '
                     'will be caught, which may lead to bugs.',
            'W0705': '\'except\' blocks are analyzed top to bottom, so if we try to catch the same '
                     'exception multiple times, only the first \'except\' block for the exception '
                     'will be reached.',
            'W0706': 'If the \'except\' block uses \'raise\' as it\'s first or only operator, it '
                     'will just raise back the exception immediately.',
            'W0711': '\'except\' can catch multiple exceptions, but they have to be passed in as a '
                     'tuple. Your exception to catch is a result of a binary operation (%s), '
                     'which will result in only one of the exceptions being caught by the  \'except\' block.',
            'W0716': '%s is not a valid operation on exceptions.'
        }
    },
    'pylint.checkers.format': {
        'FormatChecker': {
            'W0301': '\';\' in Python is used to put multiple statements on a single line, so this '
                     'semicolon is unnecessary. In general, there is no good reason to ever use a \';\' '
                     'in Python.',
            'W0312': 'This code is indented with both %ss and %ss. You should stick to just one, '
                     'but note that spaces are preferred.',
            'C0301': 'This line is %s characters long, exceeding our default limit of %s characters.',
            'C0303': 'Trailing whitespace is poor formatting, and should be removed.',
            'C0304': 'It\'s proper practice to have the final line in your file be a newline, '
                     'which it is not.',
            'C0321': 'Writing multiple statements on a single line is discouraged by PEP8.',
            'C0330': 'Wrong %s indentation%s%s.\n%s%s. This error occured because of an '
                     'inconsistent use of number of spaces for indentation.'
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
