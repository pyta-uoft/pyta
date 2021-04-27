"""Patch pylint error messages."""
from importlib import import_module

# global
patch_data = {
    'pylint.checkers.base': {
        'BasicChecker': {
            'E0111': 'reversed() can only be called on sequence types like a str, list, or tuple.',
            'W0101': 'Code after a return or raise statement will never be run, so you should '
                     'either remove this code or review the above return/raise statement(s).',
            'W0102': 'Mutable values (like %s) should not be used as a default arguments for functions. '
                     'This is a common cause of confusing and unwanted behaviour.',
            'W0104': 'This statement doesn\'t have any effect, and could be '
                     'removed without changing the behaviour of the program.',
            'W0106': 'Right now, expression %s isn\'t being used by the rest '
                     'of your code. You should either remove this expression or '
                     'save it in a variable to use it later.',
            'W0108': 'This lambda function isn\'t necessary since you can pass '
                     'the arguments directly to the function you\'re calling in '
                     'the lambda\'s body.',
            'W0109': 'Duplicate key %r in dictionary literal.',
            'W0122': 'Using exec() to evaluate code represented as a string '
                     'can be potentially dangerous, and is typically a sign of poor design.',
            'W0123': 'Using eval() to evaluate code represented as a string '
                     'can be potentially dangerous, and is typically a sign of poor design.',
            'W0126': 'This if condition references a function but is missing the parentheses '
                     'to call the function. This will cause the condition to always evaluate to True.',
            'W0199': 'Calling assert on a tuple will only evaluate to False if '
                     'it is empty. It\'s likely you intended \'assert x, y\' rather '
                     'than \'assert (x,y)\'.'
        },
        'ComparisonChecker': {
            'R0123': 'When performing a comparison with a literal, use \'==\' instead of \'is\'. '
                     'Exceptions: use \'is\' when comparing to None.',
            'C0123': 'You should use \'isinstance(x, my_type)\' instead of \'type(x) == my_type\' to '
                     'check the type of a value.'
        },
        'NameChecker': {
            'C0104': 'Disallowed name "%s". You should give your variables '
                     'meaningful rather than generic names.',
            'C0103': '%s name "%s" doesn\'t conform to %s. '
                     'Please refer to the PyTA Help Documentation for more information '
                     'on Python naming conventions.'
        },
        'PassChecker': {
            'W0107': 'Unnecessary pass statement (you can just remove this).'
        },
        'BasicErrorChecker': {
            'E0101': '__init__ is called only to initialize the attributes of a new object. '
                     'It should not return anything.',
            'E0102': '%s was already defined line %s. '
                     'You should make sure all functions, methods and classes '
                     'defined have different names.',
            'E0103': 'The %r keyword should only be used inside a loop.',
            'E0104': 'The \'return\' keyword is used to end the execution of a function '
                     'and return a result, so you should only use it inside of a function body.',
            'E0108': 'Duplicate parameter name %s in function definition.'
        }
    },
    'pylint.checkers.refactoring': {
        'RefactoringChecker':
            {'R1701': 'These multiple calls to isinstance can be merged into isinstance(%s, (%s)).',
             'R1702': 'Your code has too many nested blocks (%s, exceeding limit %s). '
                      'You should try to break it down into helper functions.',
             'R1704': 'This local variable %r should have a name different from all function parameters.',
             'R1707': 'If you mean to create a tuple here, surround the tuple expression with parentheses.',
             'R1710': 'Since this function can return a non-None value, you should '
                      'explicitly write "return None" whenever None is returned by '
                      'this function. (Possibly including at the end of the function body.)',
             'R1712': 'Use parallel assignment to swap the values of variables. '
                      'For example: to swap variables \'a\' and \'b\', simply do \'a, b = b, a\'.',
             'R1713': 'If you want to concatenate a sequence of strings, use the str.join method.',
             'R1714': 'To check whether this variable is equal to one of many values, merge the '
                      'comparisons into a single check: %r.',
             'R1715': 'To lookup a value from a dictionary if a key is present and '
                      'use a default value if the key is not, use the built-in dict.get method.',
             'R1716': 'You can simplify this boolean operation into a chained comparison. '
                      'Instead of \'a < b and b < c\', use \'a < b < c\'.',
             'R1721': 'When you want to convert a collection from one type into another, use the appropriate '
                      'type constructor instead of a comprehension. E.g., use \'list(range(1, 10))\' instead of '
                      '\'[x for x in range(1, 10)]\'.'
             },
        'NotChecker':
            {'C0113': 'Change "%s" to "%s". Removing the negation simplifies the expression.'
             },
        'RecommendationChecker':
            {'C0201': 'Rather than using \'.keys()\' to iterate over the keys of a dictionary, '
                      'you can simply iterate over the dictionary itself.'
             },
        'LenChecker':
            {'C1801': 'When checking if a collection is empty, either check equality with an empty instance '
                      'of the collection type (e.g., == []) or explicitly check that the len is equal to 0.'
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
            'R0916': 'This if condition contains too many boolean expressions '
                     '(%s, exceeding limit %s). You should see if you can reduce '
                     'the amount of expressions, or split it into branches.',
        }
    },
    'pylint.checkers.classes': {
        'ClassChecker': {
            'E0203': 'You can\'t use instance attribute %r prior to its assignment '
                     'on line %s.',
            'E0211': 'Every instance method requires at least one parameter \'self\', '
                     'referring to the object on which this method is called. ',
            'E0213': 'The first parameter of a method should always be called \'self\'. ',
            'E0241': 'This class %r should not inherit from the same class multiple times.',
            'R0201': 'This method does not make use of \'self\', so you should remove the self '
                     'parameter and move this method outside of the class (turning it into a '
                     'top-level function).',
            'R0205': 'All classes inherit from object by default, so you do not need to specify '
                     'this in the header for %r.',
            'W0211': 'The static method %r should not have \'self\' as the first parameter.',
            'W0212': 'Since %s starts with an underscore, it is considered private and so '
                     'should not be accessed outside of the class in which it is defined.',
            'W0221': 'This method must take the same number of arguments as %s %r method.',
            'W0222': 'This method\'s parameters must have the same name, order, and default '
                     'arguments as %s %r method.',
            'W0223': 'The abstract method %r in class %r must be overridden within a '
                     'concrete subclass.',
            'W0231': 'Subclass \'__init__\' method should call the \'__init__\' method from '
                     'its superclass %r.',
            'W0233': 'Subclass \'__init__\' method should call the \'__init__\' method of '
                     'the superclass rather than some unrelated class %r.',
        },
        'SpecialMethodsChecker': {
            'E0301': 'An \'__iter__\' method must return an iterator, i.e an object with a '
                     '\'__next__\' method.',
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
            'E0711': 'You mean to raise \'NotImplementedError\', which indicates that a method is abstract. ',
            'E0712': '\'except\' expects a class that is a subclass of the Exception class (%s is not).',
            'W0702': 'It\'s bad practice to use the \'except\' keyword without passing an exception, '
                     'since any and all expressions will be caught, which may lead to undetected errors '
                     'in your code.',
            'W0703': 'It\'s bad practice to use \'except: %s\' since any and all expressions '
                     'will be caught, which may lead to undetected errors in your code.',
            'W0705': '\'except\' blocks are checked top to bottom, so if we try to catch the same '
                     'exception %s multiple times, only the first \'except\' block for the exception '
                     'will be reached.',
            'W0706': 'If the \'except\' block uses \'raise\' as its first or only statement, it '
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
            'C0301': 'This line is %s characters long, exceeding the limit of %s characters.',
            'C0303': 'Trailing whitespace is poor formatting, and should be removed.',
            'C0304': 'By convention, each Python file should end with a blank line. To fix this, '
                     'go down to the bottom of your file and press Enter/Return to add an empty line.',
            'C0321': 'Avoid writing multiple statements on a single line. '
                     'This makes your code harder to understand.',
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
            'W0404': 'Module %r was re-imported on line %s. A module should not be '
                     'imported more than once.',
            'W0410': 'Imports of \'__future__\' must be the first non-docstring statement in the module.',
            'C0410': 'Import each module on line %s on separately, one per line.',
            'C0414': 'The \'import as\' is used to import a module and give it a different name in this file. '
                     'If you don\'t want to rename the module, simply use \'import\' instead.'
        }
    },
    'pylint.checkers.newstyle': {
        'NewStyleConflictChecker': {
            'E1003': 'The first argument to \'super\' should be the current class. '
                     'The argument %r is not valid.'
        }
    },
    'pylint.checkers.stdlib': {
        'StdlibChecker': {
            'W1501': '"%s" is not a valid mode for opening a file. Common modes are \'r\' for reading a file '
                     'and \'w\' for writing to a file.'
        }
    },
    'pylint.checkers.strings': {
        'StringFormatChecker': {
            'E1307': 'The argument %r does not match type %r specified by the format string.',
            'W1309': 'This f-string does not have any {...} expressions, and so the "f" can be removed.',
                     'E1310': 'Suspicious argument in %s.%s call. Strip will remove any characters contained '
                     'in its argument, so duplicate characters are either unintended, or redundant.'
        },
        'StringConstantChecker': {
            'W1401': 'The string \'%s\' contains a backslash, but is not part of an escape sequence. '
                     'If this is not a typo, then you should make this explicit by escaping the '
                     'backslash with another backslash.',
            'W1402': 'Unicode escape being used in byte string \'%s\'. Since this is not a '
                     'unicode string, inserting unicode characters will have no effect. If '
                     'you just want to write \'\\u\', you should make this explicit by escaping '
                     'the backslash with another backslash.',
            'W1404': 'This %s has two consecutive string literals. You are likely missing a '
                     'comma between them.'
        }
    },
    'pylint.checkers.typecheck': {
        'TypeChecker': {
            'E1101': '%s %r doesn\'t have the method/attribute %r%s.',
            'E1102': '%s is not callable. You may have written unnecessary parentheses following a variable.',
            'E1126': 'Objects can only be indexed by ints, slices, or objects with an \'__index__\' method.',
            'E1127': 'The index in a slice must be an int, \'None\', or an object with an '
                     '\'__index__\' method.',
            'E1129': 'The object after the \'with\' keyword must be an instance of a type that implements the '
                     '\'__enter__\' and \'__exit__\', methods, which type %s does not.',
            'E1131': '%s. The binary operation can\'t be performed on the two operands provided.',
            'E1136': '%s does not support indexing.',
            'E1140': 'Dictionary keys must be immutable.',
            'E1141': 'If you want to iterate through the (key, value) pairs of a dictionary, you need to write '
                     '\'for key, value in my_dict.items()\'.',
            'W1114': 'The arguments in this function call aren\'t in the same order as the parameters in the function '
                     'definition.'
        },
        'IterableChecker': {
            'E1133': 'Can not iterate over %s as it is not an instance of an iterable type.'
        }
    },
    'pylint.checkers.variables': {
        'VariablesChecker': {
            'E0601': 'The variable %r may be accessed prior to it having a value assigned.',
            'E0611': 'Can\'t find the name %r to import from module %r.',
            'E0633': 'Trying to assign multiple values from%s, but it is not a sequence.',
            'W0604': 'Every global variable can be referenced from the module level, so using '
                     'the \'global\' keyword at the module level has no effect.',
            'W0611': 'The import %s is unused, and so can be removed.',
            'W0612': 'The variable %s is unused and can be removed. If you intended to use it, '
                     'there may be a typo elsewhere in the code.',
            'W0613': 'The parameter %r is unused. This may indicate you misspelled a parameter name '
                     'in the function body. Otherwise, the parameter can be removed from the function '
                     'without altering the program.',
            'W0621': 'The variable name %r already refers to a variable in the outer scope defined on '
                     'line %s. This makes your code harder to read due to having to keep track of '
                     'which variable we\'re referencing.',
            'W0622': '%r is the name of a built-in function, and should not be overridden.',
            'W0631': 'Variables defined by a loop are only accessible within the loop, meaning '
                     'the variable %r is possibly undefined.',
            'W0632': 'The sequence%s is being used to assign %d variables but contains %d values.',
            'W0642': '%s is a local variable within the function. Reassigning this variable '
                     'doesn\'t mutate any objects, and so has no effect after the function ends.'
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
