# PythonTA Checks

This page describes in greater detail the errors that PythonTA checks for.
If anything is unclear, incorrect, or missing, please don't hesitate to send an
email to \[david at cs dot toronto dot edu\].

## Improper Python usage

These errors generally indicate a misuse of variables, control flow, or other Python features in our
code.

### Used before assignment (E0601) [](#E0601)

This error occurs when we are using a variable before it has been assigned a value.

```{literalinclude} /../examples/pylint/E0601_used_before_assignment.py
```

### Undefined variable (E0602) [](#E0602)

This error occurs when we are using a variable that has not been defined.

```{literalinclude} /../examples/pylint/E0602_undefined_variable.py
```

### Undefined loop variable (W0631) [](#W0631)

This error occurs when a loop variable is used outside the `for` loop where it was defined.

```{literalinclude} /../examples/pylint/W0631_undefined_loop_variable.py
```

Python, unlike many other languages (e.g. C, C++, Java), allows loop variables to be accessed
outside the loop in which they were defined. However, this practice is discouraged, as it can lead
to obscure and hard-to-detect bugs.

**See also**:

- [The scope of index variables in Python's for loops]

### Not in loop (E0103) [](#E0103)

This error occurs when the `break` or `continue` keyword is used outside of a loop. The
keyword `break` is used to exit a loop early and the keyword `continue` is used to skip an iteration
in a loop. Hence, both keywords only belong inside loops.

```{literalinclude} /../examples/pylint/E0103_not_in_loop.py
```

A common source of this error is when the `break` or `continue` is not indented properly (it must be
indented to be considered part of the loop body).

### Return outside function (E0104) [](#E0104)

This error occurs when a `return` statement is found outside a function or method.

```{literalinclude} /../examples/pylint/E0104_return_outside_function.py
```

A common source of this error is when the `return` is not indented properly (it must be indented to
be considered part of the loop body).

### Unreachable (W0101) [](#W0101)

This error occurs when there is some code after a `return` or `raise` statement. This code will
never be run, so either it should be removed, or the function is returning too early.

```{literalinclude} /../examples/pylint/W0101_unreachable.py
```

### Duplicate key (W0109) [](#W0109)

This error occurs when a dictionary literal sets the same key multiple times.

```{literalinclude} /../examples/pylint/W0109_duplicate_key.py
```

Dictionaries map unique keys to values. When different values are assigned to the same key, the last
assignment takes precedence. This is rarely what the user wants when they are constructing a
dictionary.

### Unexpected keyword arg (E1123) [](#E1123)

This error occurs when a function call passes a keyword argument which does not match the signature
of the function being called.

```{literalinclude} /../examples/pylint/E1123_unexpected_keyword_arg.py
```

Corrected version:

```python
print_greeting(name="Arthur")
```

## Type errors

These errors are some of the most common errors we encounter in Python. They generally have to do
with using a value of one type where another type is required.

### No member (E1101) [](#E1101)

This error occurs when we use dot notation (`my_var.x`) to access an attribute or to call a method
which does not exist for the given object. This can happen both for built-in types like `str` and
for classes that we define ourselves. This error often results in
an [`AttributeError`][AttributeError] when we run the code.

```{literalinclude} /../examples/pylint/E1101_no_member.py
```

### Not callable (E1102) [](#E1102)

This error occurs when we try to call a value which is not a function, method, or callable object.
In the following example, we should not call `x()` because `x` refers to an integer, and calling an
integer has no meaning.

```{literalinclude} /../examples/pylint/E1102_not_callable.py
```

### Assignment from no return (E1111) [](#E1111)

This error occurs when we assign a variable to the return value of a function call, but the function
never returns anything. In the following example, `add_fruit` mutates `fruit_basket` instead of
returning a new list. As a result, `new_fruit_basket` always gets the value `None`.

```{literalinclude} /../examples/pylint/E1111_assignment_from_no_return.py
```

We should either modify `add_fruit` to return a new list, or call `add_fruit` without assigning the
return value to a variable.

### Assignment from None (E1128) [](#E1128)

This error occurs when we assign a variable the return value of a function call, but the function
always returns `None`. In the following example, `add_fruit` always returns `None`. As a
result, `new_fruit_basket` will always get the value `None`.

```{literalinclude} /../examples/pylint/E1128_assignment_from_none.py
```

### No value for parameter (E1120) [](#E1120)

A function must be called with one argument value per parameter in its header. This error indicates
that we called a function with too few arguments. In the following example, there should be *three*
values passed to the function instead of two.

```{literalinclude} /../examples/pylint/E1120_no_value_for_parameter.py
```

Corrected version:

```python
get_sum(1, 2, 3)
```

### Too many function args (E1121) [](#E1121)

A function must be called with one argument value per parameter in its header. This error indicates
that we called a function with too many arguments. In the following example, there should be *two*
values passed to the function instead of three.

```{literalinclude} /../examples/pylint/E1121_too_many_function_args.py
```

Corrected version:

```python
get_sum(1, 2)
```

### Invalid sequence index (E1126) [](#E1126)

This error occurs when a list or tuple is indexed using the square bracket notation `my_list[...]`,
but the value of the index is not an integer.

Remember that the index indicates the *position* of the item in the list/tuple.

```{literalinclude} /../examples/pylint/E1126_invalid_sequence_index.py
```

Corrected version:

```python
a = ['p', 'y', 'T', 'A']
print(a[0])
```

### Invalid slice index (E1127) [](#E1127)

This error occurs when a list or tuple is sliced using the square bracket
notation `my_list[... : ...]`, but the two values on the left and right of the colon are not
integers.

Remember that the slice numbers indicate the *start* and *stop* positions for the slice in the
list/tuple.

```{literalinclude} /../examples/pylint/E1127_invalid_slice_index.py
```

Corrected version:

```python
a = ['p', 'y', 'T', 'A']
print(a[0:3])
```

### Invalid unary operand type (E1130) [](#E1130)

This error occurs when we use a [unary operator][Unary arithmetic and bitwise operations] (`+`, `-`
, `~`) on an object which does not support this operator. For example, a list does not support
negation.

```{literalinclude} /../examples/pylint/E1130_invalid_unary_operand_type.py
```

### Unsupported binary operation (E1131) [](#E1131)

This error occurs when we use a [binary arithmetic operator][Binary arithmetic operations] like `+`
or `*`, but the left and right sides are not compatible types. For example, a dictionary cannot be
added to a list.

```{literalinclude} /../examples/pylint/E1131_unsupported_binary_operation.py
```

### Unsupported membership test (E1135) [](#E1135)

This error occurs when we use the membership test `a in b`, but the type of `b` does not support
membership tests.

The standard Python types which support membership tests are strings, lists, tuples, and
dictionaries.

```{literalinclude} /../examples/pylint/E1135_unsupported_membership_test.py
```

### Unsubscriptable object (E1136) [](#E1136)

This error occurs when we try to index a value using square brackets (`a[...]`), but the type of `a`
does not support indexing (or "subscripting").

The standard Python types which support indexing are strings, lists, tuples, and dictionaries.

```{literalinclude} /../examples/pylint/E1136_unsubscriptable_object.py
```

### Unsupported assignment operation (E1137) [](#E1137)

This error occurs when we assign something to an object which does not support assignment (i.e. an
object which does not define the `__setitem__` method).

```{literalinclude} /../examples/pylint/E1137_unsupported_assignment_operation.py
```

### Unsupported delete operation (E1138) [](#E1138)

This error occurs when the `del` keyword is used to delete an item from an object which does not
support item deletion (i.e. an object that does not define the `__delitem__` special method).

```{literalinclude} /../examples/pylint/E1138_unsupported_delete_operation.py
```

Corrected version:

```python
class NamedList:

    ...  # Same as in the code above

    def __delitem__(self, name: str) -> None:
        idx = self._names.index(name)
        del self._names[idx]
        del self._values[idx]


named_list = NamedList(['a', 'b', 'c'], [1, 2, 3])
print('c' in named_list)  # Prints True
del named_list['c']
print('c' in named_list)  # Prints False
```

### Unbalanced tuple unpacking (E0632) [](#E0632)

This error occurs when we are trying to assign to multiple variables at once, but the right side has
too few or too many values in the sequence.

```{literalinclude} /../examples/pylint/E0632_unbalanced_tuple_unpacking.py
```

### Unpacking non-sequence (E0633) [](#E0633)

This error occurs when we are trying to assign to multiple variables at once, but the right side is
not a sequence, and so can't be unpacked.

```{literalinclude} /../examples/pylint/E0633_unpacking_non_sequence.py
```

### Not an iterable (E1133) [](#E1133)

This error occurs when a non-iterable value is used in a place where an iterable is expected.
An [iterable][Python Documentation: iterable] is an object capable of returning its members one at a
time. Examples of iterables include sequence types such as `list`, `str`, and `tuple`, some
non-sequence types such as `dict`, and instances of other classes which define the `__iter__`
or `__getitem__` special methods.

```{literalinclude} /../examples/pylint/E1133_not_an_iterable.py
```

Corrected version:

```python
for number in [1, 2, 3]:
    print(number)
```

### Not a mapping (E1134) [](#E1134)

This error occurs when a non-mapping value is used in a place where mapping is expected. This is a result of unpacking a non-dict with `**` in a function call meaning that the parameters are unfilled. 

`**` can only be used on a `dict` to unpack the values. 

```{literalinclude} /../examples/pylint/E1134_not_a_mapping.py
```

## Code complexity

### Unneeded not (C0113) [](#C0113)

This error occurs when a boolean expression contains an unneeded negation. If we are getting this
error, the expression can be simplified to not use a negation.

```{literalinclude} /../examples/pylint/C0113_unneeded_not.py
```

The above can be modified to:

```python
number = 5
if number < 0:
    number_category = 'negative'
else:
    number_category = 'non-negative'
```

### Simplifiable condition (R1726) [](#R1726)

This error occurs when a boolean test condition can be simplified.
Test conditions are expressions evaluated inside of statements such as `if`, `while`, or `assert`.

```{literalinclude} /../examples/pylint/R1726_simplifiable_condition.py
```

The above can be modified to:

```python
if a:  # Error was on this line
  pass
```

### Condition evals to constant (R1727) [](#R1727)

This error occurs when a boolean test condition always evaluates to a constant.
Test conditions are expressions evaluated inside of statements such as `if`, `while`, or `assert`.

```{literalinclude} /../examples/pylint/R1727_condition_evals_to_constant.py
```

The above can be modified to:

```python
if True:  # Error was on this line
  pass
```

### Singleton comparison (C0121) [](#C0121)

This error occurs when an expression is compared to a singleton value like `True`, `False` or `None`
.

Here is an example involving a comparison to `None`:

```{literalinclude} /../examples/pylint/C0121_singleton_comparison.py
```

The above can be modified to:

```python
def square(number: Optional[float]) -> Optional[float]:
    """Return the square of the number."""
    if number is None:
        return None
    else:
        return number ** 2
```

On the other hand, if you are comparing a boolean value to `True` or `False`, you can actually omit
the comparison entirely:

```python
# Bad
def square_if_even(number: int) -> int:
    if (number % 2 == 0) == True:
        return number ** 2
    else:
        return number


# Good
def square_if_even(number: int) -> int:
    if number % 2 == 0:
        return number ** 2
    else:
        return number
```

**See also**:

- [The story of None, True and False (and an explanation of literals, keywords and builtins thrown in)][The story of None, True and False]

### Using constant test (W0125) [](#W0125)

This error occurs when a conditional statement (like an `if` statement) uses a constant value for
its test. In such a case, a conditional statement is not necessary, as it will always result in the
same path of execution.

```{literalinclude} /../examples/pylint/W0125_using_constant_test.py
```

### Redeclared Assigned Name (W0128) [](#W0128)

This error occurs when a variable is redeclared on the same line it was assigned.

```{literalinclude} /../examples/pylint/W0128_redeclared_assigned_name.py
```

### Too many branches (R0912) [](#R0912)

The function or method has too many branches, making it hard to follow. This is a sign that the
function/method is too complex, and should be split up.

**Note**: The checker limit is 12 branches.

```{literalinclude} /../examples/pylint/R0912_too_many_branches.py
```

### Too many nested blocks (R1702) [](#R1702)

This error occurs when we have more than three levels of nested blocks in our code. Deep nesting is
a sign that our function or method is too complex, and should be broken down using helper functions
or rewritten as a [list comprehension][list comprehensions tutorial].

**Note**: This checker does not count function, method, or class definitions as blocks, so the
example below is considered to have *six* nested blocks, not seven.

```{literalinclude} /../examples/pylint/R1702_too_many_nested_blocks.py
```

The code above can be fixed using a helper function:

```python
def drop_none(lst: List[Optional[int]]) -> List[int]:
    """Return a copy of `lst` with all `None` elements removed."""
    new_lst = []
    for element in lst:
        if element is not None:
            new_lst.append(element)
    return new_lst


def cross_join(x_list: List[Optional[int]], y_list: List[Optional[int]],
               z_list: List[Optional[int]]) -> List[Tuple[int, int, int]]:
    """Perform an all-by-all join of all elements in the input lists."""
    cross_join_list = []
    for x in drop_none(x_list):
        for y in drop_none(y_list):
            for z in drop_none(z_list):
                cross_join_list.append((x, y, z))
    return cross_join_list
```

or using list comprehension:

```python
def cross_join(x_list: List[Optional[int]], y_list: List[Optional[int]],
               z_list: List[Optional[int]]) -> List[Tuple[int, int, int]]:
    """Perform an all-by-all join of all elements in the input lists."""
    cross_join_list = [
        (x, y, z)
        for x in x_list
        if x is not None
        for y in y_list
        if y is not None
        for z in z_list
        if z is not None
    ]
    return cross_join_list
```

### Too many lines (C0302) [](#C0302)

This error occurs when the file has too many lines. The limit for too many lines is specified
through the `max-module-lines` configuration option. 

**Note**: The default value is `1000`.

### Too many arguments (R0913) [](#R0913)

The function or method is defined with too many arguments. This is a sign that the function/method
is too complex, and should be split up, or that some of the arguments are related, and should be
combined and passed as a single object.

**Note**: The checker limit is 5 arguments.

```{literalinclude} /../examples/pylint/R0913_too_many_arguments.py
```

### Too many locals (R0914) [](#R0914)

The function or method has too many local variables.

**Note**: The checker limit is 15 local variables.

```{literalinclude} /../examples/pylint/R0914_too_many_locals.py
```

### Too many statements (R0915) [](#R0915)

The function or method has too many statements. We should split it into smaller functions/methods.

**Note**:

- The checker limit is 50 statements.
- Comments do not count as statements.

```{literalinclude} /../examples/pylint/R0915_too_many_statements.py
```

### Unused variable (W0612) [](#W0612)

This error occurs when we have a defined variable that is never used.

```{literalinclude} /../examples/pylint/W0612_unused_variable.py
```

### Unused argument (W0613) [](#W0613)

This error occurs when a function argument is never used in the function.

```{literalinclude} /../examples/pylint/W0613_unused_argument.py
```

### Pointless statement (W0104) [](#W0104)

This error occurs when a statement does not have any effect. This means that the statement could be
removed without changing the behaviour of the program.

```{literalinclude} /../examples/pylint/W0104_pointless_statement.py
```

### Pointless string statement (W0105) [](#W0105)

This error occurs when a string statement does not have any effect.  Very similar to error `W0104`, but 
for strings.

```{literalinclude} /../examples/pylint/W0105_pointless_string_statement.py
```

### Unnecessary pass (W0107) [](#W0107)

This error occurs when a [`pass` statement][`pass` statements] is used that can be avoided (or has
no effect). `pass` statements should only be used to fill what would otherwise be an empty code
block, since code blocks cannot be empty in Python.

```{literalinclude} /../examples/pylint/W0107_unnecessary_pass.py
```

In the above example, the `pass` statement is "unnecessary" as the program's effect is not changed
if `pass` is removed.

**See also:**

- [StackOverflow: How To Use The Pass Statement In Python]

### Inconsistent return statements (R1710) [](#R1710)

This error occurs when you have a function that sometimes returns a non-`None` value and sometimes *
implicitly* returns `None`. This is an issue because in Python, we prefer making code explicit
rather than implicit.

```{literalinclude} /../examples/pylint/R1710_inconsistent_return_statements.py
```

In `add_sqrts`, we should change `return` into `return None` to make better contrast the return
value with the other branch. In the other two functions, it's possible that none of the `return`
statements will execute, and so the end of the function body will be reached, causing a `None` to be
returned implicitly.
(Forgetting about this behaviour actually is a common source of bugs in student code!)
In both cases, you can fix the problem by adding an explicit `return None` to the end of the
function body.

In CSC148, you may sometimes choose resolve this error by instead *raising an error* rather than
returning `None`.

### Consider using with (R1732) [](#R1732)

This error occurs when a resource allocating operation such as opening a file can be replaced by a `with` block. By using `with`, the file is closed automatically which saves resources. 

```{literalinclude} /../examples/pylint/R1732_consider_using_with.py
```

Corrected version: 
```python
with open('my_file.txt', 'r') as file:
    ... # No need to manually close the file 
```

## Documentation and naming

Good documentation and identifiers are essential for writing software. PyTA helps check to make sure
we haven't forgotten to document anything, as well as a basic check on the formatting of our
identifiers.

### Empty Docstring (C0112) [](#C0112)

This error occurs when a module, function, class or method has an empty docstring.

```{literalinclude} /../examples/pylint/C0112_empty_docstring.py
```

### Invalid name (C0103) [](#C0103)

This error occurs when a name does not follow
the [Python Naming Convention][PEP8: Naming Conventions] associated with its role (constant,
variable, etc.).

- Names of variables, attributes, methods, and arguments should be
  in **`lowercase_with_underscores`**.
- Names of constants should be in **`ALL_CAPS_WITH_UNDERSCORES`**.
- Names of classes should be in **`CamelCase`**.

A special character accepted in all types of names is `_`. Numbers are allowed in all names, but
names must not begin with a number.

```{literalinclude} /../examples/pylint/C0103_invalid_name.py
```

### Disallowed name (C0104) [](#C0104)

This error occurs when a variable name is chosen to be a typical generic name, rather than a
meaningful one. Here are some of the disallowed names to avoid:

- `foo`
- `bar`
- `baz`
- `toto`
- `tutu`
- `tata`

```{literalinclude} /../examples/pylint/C0104_disallowed_name.py
```

### Function redefined (E0102) [](#E0102)

This error occurs when a function, class or method is redefined. If we are getting this error, we
should make sure all the functions, methods and classes that we define have different names.

```{literalinclude} /../examples/pylint/E0102_function_redefined.py
```

### Duplicate argument name (E0108) [](#E0108)

This error occurs if there are duplicate parameter names in function definitions. All parameters
must have distinct names, so that we can refer to each one separately in the function body.

```{literalinclude} /../examples/pylint/E0108_duplicate_argument_name.py
```

### Redefined argument from local (R1704) [](#R1704)

This error occurs when a local name is redefining the name of a parameter.

```{literalinclude} /../examples/pylint/R1704_redefined_argument_from_local.py
```

Corrected version:

```python
def greet_person(name, friends) -> None:
    """Print the name of a person and all their friends."""
    print("My name is {}".format(name))
    for friend in friends:
        print("I am friends with {}".format(friend))
```

**See also**: [W0621](#W0621)

### Redefined outer name (W0621) [](#W0621)

This error occurs when we are redefining a variable name that has already been defined in the outer
scope.

For example, this error will occur when we have a local name identical to a global name. The local
name takes precedence, but it hides the global name, making it no longer accessible. Note that the
global name is not accessible *anywhere* in the function where it is redefined, even before the
redefinition.

```{literalinclude} /../examples/pylint/W0621_redefined_outer_name.py
```

### Redefined builtin (W0622) [](#W0622)

This error occurs when we are redefining a built-in function, constant, class, or exception.

```{literalinclude} /../examples/pylint/W0622_redefined_builtin.py
```

The following is a list of [builtin functions][Built-in Functions] in Python 3.6.

```text
abs                 all                 any                 ascii               bin
bool                bytearray           bytes               callable            chr
classmethod         compile             complex             copyright           credits
delattr             dict                dir                 divmod              dreload
enumerate           eval                exec                filter              float
format              frozenset           get_ipython         getattr             globals
hasattr             hash                help                hex                 id
input               int                 isinstance          issubclass          iter
len                 license             list                locals              map
max                 memoryview          min                 next                object
oct                 open                ord                 pow                 print
property            range               repr                reversed            round
set                 setattr             slice               sorted              staticmethod
str                 sum                 super               tuple               type
vars                zip
```

## Imports

There are standards governing how we should organize our imports, or even possibly which modules we
may import at all.

### Forbidden imports (E9999) [](#E9999)

This error occurs when your code imports a module which is not allowed (usually for the purpose of
an assignment/exercise).

```{literalinclude} /../examples/custom_checkers/e9999_forbidden_import.py
---
lines: 1-3
---
```

### Import error (E0401) [](#E0401)

The module is unable to be imported. Check the spelling of the module name, or whether the module is
in the correct directory.

```{literalinclude} /../examples/pylint/E0401_import_error.py
```

There are other forms of import statements that may cause this error. For example:

```python
import missing_module as foo  # This module does not exist
```

### No name in module (E0611) [](#E0611)

This error occurs when we are trying to access a variable from an imported module, but that variable
name could not be found in that referenced module.

```{literalinclude} /../examples/pylint/E0611_no_name_in_module.py
```

### Wildcard import (W0401) [](#W0401)

We should only import what we need. Wildcard imports (shown below) are generally discouraged, as
they add all objects from the imported module into the global namespace. This makes it difficult to
tell in which module a particular class, function or constant is defined, and may cause problems,
for example, when multiple modules have objects with identical names.

```{literalinclude} /../examples/pylint/W0401_wildcard_import.py
```

Rather than importing everything with wildcard `*`, we should specify the names of the objects which
we would like to import:

```python
from module_name import SOME_CONSTANT, SomeClass, some_function
```

Or, if we need to import many objects from a particular module, we can import the module itself, and
use it as a namespace for the required objects:

```python
import module_name

c = module_name.SomeClass()
```

### Reimported (W0404) [](#W0404)

A module should not be imported more than once.

```{literalinclude} /../examples/pylint/W0404_reimported.py
```

### Import self (W0406) [](#W0406)

A module should not import itself. For example, if we have a module named `W0406_import_self`, it
should not import a module with the same name.

```{literalinclude} /../examples/pylint/W0406_import_self.py
```

This error can occur when the name of our Python file conflicts with the name of a module which we
would like to import. For example, if we have a Python file named `math.py`, calling `import math`
from within that file (or from within *any* Python file in the same directory) will import *
our* `math.py` file, and not the [`math` module] from the standard library.


### Cyclic import (R0401) [](#R0401)

A module should not import a file which results in an import of the original module.

Example File 1
```{literalinclude} /../examples/pylint/R0401_cyclic_import.py
```

Example File 2
```{literalinclude} /../examples/pylint/cyclic_import_helper.py
```

### Multiple imports (C0410) [](#C0410)

Different modules should not be imported on a single line.

```{literalinclude} /../examples/pylint/C0410_multiple_imports.py
```

Rather, each module should be imported on a separate line.

```python
import sys
import math
```

Note, however, that we can import multiple functions, classes, or constants on one line, as long as
they are from the same module.

```python
from shutil import copy, SameFileError
```

### Wrong import order (C0411) [](#C0411)

This error occurs when the [PEP8 import order][PEP8 Imports] is not respected. We should do standard
library imports first, then third-party libraries, then local imports.

```{literalinclude} /../examples/pylint/C0411_wrong_import_order.py
```

### Ungrouped imports (C0412) [](#C0412)

Imports should be grouped by package.

```{literalinclude} /../examples/pylint/C0412_ungrouped_imports.py
```

Corrected version:

```python
from sys import byteorder, stdin  # Same packages should be grouped
from math import floor
```

### Wrong import position (C0413) [](#C0413)

Imports should be placed at the top of the module, above any other code, but below the module
docstring.

```{literalinclude} /../examples/pylint/C0413_wrong_import_position.py
```

### Import outside toplevel (C0415) [](#C0415)

Imports should be placed at the top-level of the module, not inside function or class bodies.

```{literalinclude} /../examples/pylint/C0415_import_outside_toplevel.py
```

### Unused import (W0611) [](#W0611)

This error occurs when we import a module which is not used anywhere in our code.

```{literalinclude} /../examples/pylint/W0611_unused_import.py
```

## Classes and objects

### Too many instance attributes (R0902) [](#R0902)

The class has too many instance attributes, which suggests that it is too complicated and tries to
do too many things.

**Note**: The checker limit is 7 instance attributes.

```{literalinclude} /../examples/pylint/R0902_too_many_instance_attributes.py
```

One solution is to logically decompose the class into multiple classes, each with fewer instance
attributes. We can then use composition to access those attributes in a different class.

```python
class Edible(object):
    """Class with a few instance attributes."""

    def __init__(self) -> None:
        self.bread = "Sourdough"
        self.liquid = "Water"


class Ownership(object):
    """Class with a few instance attributes."""

    def __init__(self) -> None:
        self.animal = "Dog"
        self.clothing = "Shirt"


class Description(object):
    """Class with a few instance attributes."""

    def __init__(self) -> None:
        self.colour = "Black"
        self.shape = "Circle"
        self.direction = "Up"
        self.number = 3


class Composition(object):
    """Class using composition to leverage other classes."""

    def __init__(self) -> None:
        self.edible = Edible()
        self.ownership = Ownership()
        self.description = Description()
```

**See also**: [R0914](#R0914)

### Abstract method (W0223) [](#W0223)

This error occurs when an abstract method (i.e. a method with a `raise NotImplementedError`
statement) is not overridden inside a subclass of the abstract class.

```{literalinclude} /../examples/pylint/W0223_abstract_method.py
```

Corrected version:

```python
class Cat(Animal):
    """A worthy companion."""

    def make_sound(self) -> str:
        return 'Miew...'
```

### Arguments differ (W0221) [](#W0221)

This error occurs when a method takes a different number of arguments than the interface that it
implements or the method that it overrides.

```{literalinclude} /../examples/pylint/W0221_arguments_differ.py
```

Corrected version:

```python
class Dog(Animal):
    """A man's best friend."""

    def make_sound(self, mood: str) -> None:
        if mood == 'happy':
            print("Woof Woof!")
        elif mood == 'angry':
            print("Grrrrrrr!!")
```

### Different method signature (W0222) [](#W0222)

When a child class overrides a method of the parent class, the new method should have the same
signature as the method which it is overriding. In other words, the names and the order of the
parameters should be the same in the two methods. Furthermore, if a parameter in the parent method
has a default argument, it must also have a default argument in the child method.

```{literalinclude} /../examples/pylint/W0222_signature_differs.py
```

Corrected version:

```python
class PremiumBankAccount(StandardBankAccount):
    ...

    def withdraw(self, amount: float = 200) -> float:  # Note the default argument
        ...
```

### Return in `__init__` (E0101) [](#E0101)

This error occurs when the [`__init__`] method contains a return statement.

The purpose of the `__init__` method is to initialize the attributes of an object. `__init__` is
called by the special method [`__new__`] when a new object is being instantiated, and `__new__` will
raise a `TypeError` if `__init__` returns anything other than `None`.

```{literalinclude} /../examples/pylint/E0101_return_in_init.py
```

### Protected member access (W0212) [](#W0212)

Attributes and methods whose name starts with an underscore should be considered "private" and
should not be accessed outside of the class in which they are defined.

```{literalinclude} /../examples/pylint/W0212_protected_access.py
```

Private attributes and methods can be modified, added, or removed by the maintainer of the class at
any time, which makes external code which uses those attributes or methods fragile. Furthermore,
modifying a private attribute or calling a private method may lead to undefined behavior from the
class.

### Bad parent init (W0233) [](#W0233)

When using inheritance, we should call the `__init__` method of the parent class and not of some
unrelated class.

```{literalinclude} /../examples/pylint/W0233_non_parent_init_called.py
```

To fix this, call the `__init__` method of the parent class.

```python
class Child(Parent):
    """A child class."""

    def __init__(self) -> None:
        Parent.__init__(self)
```

Another option is to use [`super()`][super].

```python
class Child(Parent):
    """A child class."""

    def __init__(self) -> None:
        super().__init__()
```

**See also**:

- [Super considered super!]
- [Python's super considered harmful]
- [StackOverflow: What does 'super' do in Python?]

### Super with arguments (R1725) [](#R1725)

This error occurs when calling `super()` with the class and instance as these can be ommited from
Python 3.

```{literalinclude} /../examples/pylint/R1725_super_with_arguments.py
```

Corrected Version:

```python
class DummyClass:
    def __init__(self):
        super().__init__()  # Error was on this line
```

### Attribute defined outside init (W0201) [](#W0201)

Any attribute we define for a class should be created inside the `__init__` method. Defining it
outside this method is considered bad practice, as it makes it harder to keep track of what
attributes the class actually has.

```{literalinclude} /../examples/pylint/W0201_attribute_defined_outside_init.py
```

We should do this instead:

```python
class SomeNumbers:
    """A class to store some numbers."""

    def __init__(self) -> None:
        self.num = 1
        self.other_num = None

    def set_other_num(self, other_num: int) -> None:
        self.other_num = other_num
```

### Method hidden (E0202) [](#E0202)

If we accidentally hide a method with an attribute, it can cause other code to attempt to invoke
what it believes to be a method, which will fail since it has become an attribute instead. This will
cause the program to raise an error.

```{literalinclude} /../examples/pylint/E0202_method_hidden.py
```

### Access to member before definition (E0203) [](#E0203)

Before trying to use a member of a class, it should have been defined at some point. If we try to
use it before assigning to it, an error will occur.

```{literalinclude} /../examples/pylint/E0203_access_member_before_definition.py
```

### Unexpected special method signature (E0302) [](#E0302)

This error occurs when a special method (also known as
a ["dunder method"][Python double-under, double-wonder], because it has double underscores or "
dunders" on both sides) does not have the expected number of parameters. Special methods have an
expected signature, and if we create a method with the same name and a different number of
parameters, it can break existing code and lead to errors.

```{literalinclude} /../examples/pylint/E0302_unexpected_special_method_signature.py
```

Corrected version:

```python
class Animal:
    """A carbon-based life form that eats and moves around."""
    _name: str

    def __init__(self, name: str) -> None:
        self._name = name

    def __str__(self) -> str:
        return '<Animal({})>'.format(self._name)
```

### Inheriting from a non-class (E0239) [](#E0239)

A new class can only inherit from a different class (i.e. a Python object which defines the *type*
of an object). It cannot inherit from an instance of a class or from a Python literal such as a
string, list, or dictionary literal.

```{literalinclude} /../examples/pylint/E0239_inherit_non_class.py
```

Corrected version:

```python
class FancyFloat(float):
    """A fancy floating point number."""
    pass
```

### Duplicate bases (E0241) [](#E0241)

A class should not inherit from a different class multiple times.

```{literalinclude} /../examples/pylint/E0241_duplicate_bases.py
```

### No method argument (E0211) [](#E0211)

Each method in a class needs to have at least one parameter, which by convention we name `self`.
When we create an instance of a class and call an instance method, Python automatically passes the
class instance as the first argument to the method. If a method does not expect any arguments, this
will result in an error.

```{literalinclude} /../examples/pylint/E0211_no_method_argument.py
```

Corrected version:

```python
class Saxophone:
    """A jazzy musical instrument."""

    def __init__(self) -> None:
        self._sound = "Saxamaphone...."

    def make_sound(self) -> None:
        print(self._sound)
```

### `self` as the first argument (E0213) [](#E0213)

The first parameter of a method should always be called `self`. While it is possible to name the
first parameter something else, using the word `self` is a convention that is strongly adhered to by
the Python community and makes it clear that we did not simply forget to add `self` or accidentally
intended a function as a method.

```{literalinclude} /../examples/pylint/E0213_no_self_argument.py
```

Corrected version:

```python
class SecretKeeper:
    """A class which stores a secret as a private attribute."""

    def __init__(self, secret: str) -> None:
        self._secret = secret

    def guess_secret(self, secret) -> bool:
        """Guess the private secret."""
        return self._secret == secret
```

### No self use (R0201) [](#R0201)

If a method does not make use of the first argument `self`, it means that the task that the method
is performing is not linked to the class of which it is a member. In such a case, we should rewrite
the method as a function (by removing the first parameter `self`) and move it outside the class.

In the following example, `add_small_coins` does not make use of the first parameter `self` and so
can be moved outside the class as a function.

```{literalinclude} /../examples/pylint/R0201_no_self_use.py
```

Corrected version:

```python
class CashRegister:
    """A cash register for storing money and making change."""
    _current_balance: float

    def __init__(self, balance: float) -> None:
        self._current_balance = balance


def add_small_coins(nickels: int = 0, dimes: int = 0, quarters: int = 0) -> float:
    """Return the dollar value of the small coins."""
    return 0.05 * nickels + 0.10 * dimes + 0.25 * quarters
```

**See also**:

- [W0211](#W0211)

### Bad static method argument (W0211) [](#W0211)

This error occurs when a static method has `self` as the first parameter. Static methods are methods
that do not operate on instances. If we feel that the logic of a particular function belongs inside
a class, we can move that function into the class and add
a [`@staticmethod`][Python Documentation: staticmethod] [decorator][Python Documentation: decorator]
to signal that the method is a static method which does not take a class instance as the first
argument. If such a static method contains `self` as the first parameter, it suggests that we are
erroneously expecting a class instance as the first argument to the method.

```{literalinclude} /../examples/pylint/W0211_bad_staticmethod_argument.py
```

Corrected version:

```python
class CashRegister:
    """A cash register for storing money and making change."""
    _current_balance: float

    def __init__(self, balance: float) -> None:
        self._current_balance = balance

    @staticmethod
    def add_small_coins(nickels: int = 0, dimes: int = 0, quarters: int = 0) -> float:
        """Return the dollar value of the small coins."""
        return 0.05 * nickels + 0.10 * dimes + 0.25 * quarters
```

**See also**:

- [R0201](#R0201)
- [StackOverflow: What is the difference between `@staticmethod` and `@classmethod` in Python?]

## Exceptions

### Bare exception (W0702) [](#W0702)

If the `except` keyword is used without being passed an exception, *all exceptions will be caught*.
This is not good practice, since we may catch exceptions that we do not want to catch. For example,
we typically do not want to catch the [`KeyboardInterrupt`][Python Documentation: KeyboardInterrupt]
exception, which is thrown when a user attempts to exist the program by typing `Ctrl-C`.

```{literalinclude} /../examples/pylint/W0702_bare_except.py
```

### Exception is too generic (W0703) [](#W0703)

Using `except Exception:` is only slightly more specific than `except:` and should also be avoided (
see [W0702](#W0702)). Since most builtin exceptions, and all user-defined exceptions, are derived
from the `Exception` class, using `except Exception:` provides no information regarding which
exception actually occurred. Exceptions which we do not expect can go unnoticed, and this may lead
to bugs.

```{literalinclude} /../examples/pylint/W0703_broad_except.py
```

### Duplicate except blocks (W0705) [](#W0705)

This error occurs when we try to catch the same exception multiple times. Only the first `except`
block for a particular exception will be reached.

```{literalinclude} /../examples/pylint/W0705_duplicate_except.py
```

### Bad exception order (E0701) [](#E0701)

Except blocks are analyzed sequentially (from top to bottom) and the first block that meets the
criteria for catching the exception will be used. This means that if we have a generic exception
type before a specific exception type, the code for the specific exception type will never be
reached.

```{literalinclude} /../examples/pylint/E0701_bad_except_order.py
```

### Binary op exception (W0711) [](#W0711)

The Python `except` statement can catch multiple exceptions, if those exceptions are passed as a
tuple. It is possible (but incorrect!) to pass `except` an expression containing the exception
classes separated by a binary operator such as `and` or `or`. In such a case, only one of the
exceptions will be caught!

```{literalinclude} /../examples/pylint/W0711_binary_op_exception.py
```

Corrected version:

```python
def divide_and_square(numerator: float, denominator: float) -> float:
    """Divide the numerator by the denominator and square the result."""
    try:
        return (numerator / denominator) ** 2
    except (ZeroDivisionError, OverflowError):
        return float('nan')
```

### Misplaced bare raise (E0704) [](#E0704)

The Python `raise` statement can be used without an expression only inside an `except` block. In
this case, it will re-raise the exception that was caught by the `except` block. This may be useful
if, for example, we wish to do some cleanup (e.g. close file handles), or print an error message,
before passing the exception up the call stack.

```{literalinclude} /../examples/pylint/E0704_misplaced_bare_raise.py
```

Corrected version:

```python
def divide(numerator: float, denominator: float) -> float:
    """Divide the numerator by the denominator."""
    try:
        return numerator / denominator
    except ZeroDivisionError:
        print("Can't divide by 0!")
        raise
```

### Raising bad type (E0702) [](#E0702)

The Python `raise` statement expects an object that is derived from
the [`BaseException`][Python Documentation: BaseException] class. We cannot call `raise` on integers
or strings.

```{literalinclude} /../examples/pylint/E0702_raising_bad_type.py
```

**See also**: [E0710](#E0710)

### Raising non-exception (E0710) [](#E0710)

The Python `raise` statement expects an object that is derived from
the [`BaseException`][Python Documentation: BaseException] class. All user-defined exceptions should
inherit from the [`Exception`][Python Documentation: Exception] class (which will make them indirect
descendents of the `BaseException` class). Attempting to raise any other object will lead to an
error.

```{literalinclude} /../examples/pylint/E0710_raising_non_exception.py
```

### NotImplemented raised (E0711) [](#E0711)

[`NotImplemented`][Python Documentation: NotImplemented] should only be used as a return value for
binary special methods, such as `__eq__`, `__lt__`, `__add__`, etc., to indicate that the operation
is not implemented with respect to the other type. It is *not interchangeable*
with [`NotImplementedError`][Python Documentation: NotImplementedError], which should be used to
indicate that the abstract method must be implemented by the derived class.

```{literalinclude} /../examples/pylint/E0711_notimplemented_raised.py
```

### Catching non-exception (E0712) [](#E0712)

The Python `raise` statement expects an object that is derived from
the [`BaseException`][Python Documentation: BaseException] class (see [E0710](#E0710)). Accordingly,
the Python `except` statement also expects objects that are derived from
the [`BaseException`][Python Documentation: BaseException] class. Attempting to call `except` on any
other object will lead to an error.

```{literalinclude} /../examples/pylint/E0712_catching_non_exception.py
```

## Custom errors

### Global variables (E9997) [](#E9997)

When writing Python programs, your variables should always be defined within functions.
(A *global variable* is a variable that isn't defined within a function.)

Example:

```{literalinclude} /../examples/custom_checkers/E9997_global_variables.py
---
lines: 16-20
---
```

Global variables should be avoided because they can be changed by other functions, which causes
unpredictable behaviour in your program. You can indicate that a global variable shouldn't be
changed by naming it using the `ALL_CAPS` naming style:

```python
EX = 1


def add_ex(n: int) -> int:
  """Add EX to n."""
  return EX + n
```

We call variables that are named using this style **constants**, and expect that they don't change
when we run our code. PythonTA allows global constants, and so would not report the
`forbidden-global-variables` error on our second example. 

**See also**: [Global Variables Are Bad]

### Forbidden IO function (E9998) [](#E9998)

Input / output functions ([`input`], [`open`] and [`print`]) should not be used unless explicitly
required. If `print` calls are used to debug the code, they should be removed prior to submission.

Example:

```{literalinclude} /../examples/custom_checkers/E9998_forbidden_io_function.py
```

### Loop iterates only once (E9996) [](#E9996)

This error occurs when a loop will only ever iterate once. This occurs when every possible
execution path through the loop body ends in a `return` statement (or another type of statement
that ends the loop, like `break`).

Example:

```python
def all_even(nums: list[int]) -> bool:
    """Return whether nums contains only even numbers."""
    for num in nums:      # This loop will only ever run for one iteration before returning. 
        if num % 2 == 0:
            return True
        else:
            return False
```

In this example, the return value of `all_even` is based only on the first number in `nums`, and none
of the other list elements are checked. This version would incorrectly return `True` on the list `[2, 3]`.
Here is a corrected version of this function:

```python
def all_even(nums: list[int]) -> bool:
    """Return whether nums contains only even numbers."""
    for num in nums:      # This loop will only ever run for one iteration before returning. 
        if num % 2 != 0:
            return False

    return True
```

By moving the `return True` to outside the loop, we ensure that the only way `True` is returned is
when there are only even numbers in the list.

### Invalid Range Index (E9993) [](#E9993)

This error occurs when we call the `range` function but with argument(s) that would cause the range
to be empty or only have one element.

Examples:

```{literalinclude} /../examples/custom_checkers/e9993_invalid_range_index.py
```

When such `range`s are used with a loop, the loop will iterate either zero or one time, which is
almost certainly not what we intended! This usually indicates an error with how `range` is called.

### Unnecessary Indexing (E9994) [](#E9994)

This error occurs when we use a for loop that goes over a range of indexes for a list, but only use
those indexes to access elements from the list.

Example:

```{literalinclude} /../examples/custom_checkers/e9994_unnecessary_indexing.py
---
lines: 5-11
---
```

We can simplify the above code by changing the loop to go over the elements of the list directly:

```python
def sum_items(lst: List[int]) -> int:
    """Return the sum of a list of numbers."""
    s = 0
    for x in lst:
        s += x

    return s
```

In general, we should only loop over indexes (`for i in range(len(lst))`) if we are using the index
for some purpose other than indexing into the list.
One common example is if we want to loop over two lists in parallel:

```python
def print_sum(lst1: List[int], lst2: List[int]) -> None:
    """Print the sums of each corresponding pair of items in lst1 and lst2.
    Precondition: lst1 and lst2 have the same length.
    """
    for i in range(len(lst1)):
        print(lst1[i] + lst2[i])
```

### For Target Subscript (E9984) [](#E9984)

This error occurs when a for loop variable uses indexing notation, which can occur if you mix up the
loop variable and the list being iterated over.

Examples:

```{literalinclude} /../examples/custom_checkers/e9984_invalid_for_target.py
---
lines: 5-10
---
```

To fix this, always use a brand-new variable name with a for loop.
For example:

```python
def example1(lst: List[int]) -> int:
    s = 0
    for number in lst:  # Fixed
        s += number
    return s
```

### Possibly undefined variable (E9969) [](#E9969)

This error occurs when we use a variable that might not be defined prior to its use.
The most common cause is when we define a variable in one branch of an if statement, but not another.

Example:

```{literalinclude} /../examples/custom_checkers/e9969_possibly_undefined.py
```

### Redundant assignment (E9959) [](#E9959)

This error occurs when we have two assignment statements to the same variable, without using that
variable in between the assignment statement. In this case, the first statement is redundant, since
it gets overridden by the second.

Example:

```python
x = 10  # This assignment statement is redundant
y = 5
x = 1
print(x)
```

### Shadowing in comprehension (E9988) [](#E9988)

This error occurs when a variable in a comprehension shadows (i.e., has the same name as) a variable
from an outer scope, such as a local variable in the same function.
In general you should avoid reusing variable names within the same function, and so you can fix this
error by renaming the variable in the comprehension.

Example:

```{literalinclude} /../examples/custom_checkers/e9988_shadowing_in_comprehension.py
---
lines: 10-12
---
```

### Missing parameter type (E9970) [](#E9970)

This error occurs when we have written a function definition but are missing a type annotation for
a parameter.

Example:

```{literalinclude} /../examples/custom_checkers/e9970_missing_param_type.py
---
lines: 2-4
---
```

### Missing return type (E9971) [](#E9971)

This error occurs when we have written a function definition but are missing a type annotation for 
the return value. Use `None` as the type annotation if the function does not return anything.

Example:

```{literalinclude} /../examples/custom_checkers/e9971_missing_return_type.py
---
lines: 2-4
---
```

### Missing attribute type (E9972) [](#E9972)

This error occurs when we have written a class but are missing a type annotation for an 
instance attribute assigned in the class initializer.

Example:

```{literalinclude} /../examples/custom_checkers/e9972_missing_attribute_type.py
---
lines: 4-9
---
```

These type annotations should be written at the top of the class body.
For example:

```python
class ExampleClass:
    """Class docstring."""
    inst_attr: str
    inst_attr2: bool
    
    def __init__(self):  # Missing return type annotation
        """Initialize a new instance of this class."""
        self.inst_attr = 'hi'
        self.inst_attr2 = True
```

### Missing space in doctest (E9973) [](#E9973)

This error occurs when a doctest found in the docstring of a function is not followed by a space.
In this case the doctest will not actually be parsed. 

Example:
```{literalinclude} /../examples/custom_checkers/e9973_missing_space_in_doctest.py
---
lines: 4-9
---
```

This can simply be corrected by adding a space before the code be executed:
```
def f(x: int) -> int:
    """Return one plus x.

    >>> f(10)  # Adding a space will allow the doctest to be parsed. 
    11
    """
```

### Pycodestyle errors (E9989) [](#E9989)

These errors are based on the Python code style guidelines ("PEP8") published by the Python team.
These errors do not affect the functionality of your code, but can affect its readability.
The error messages display how to fix them (e.g., by adding spaces or adding/removing blank lines).

See also: [PEP 8 -- Style Guide for Python Code](https://www.python.org/dev/peps/pep-0008/)

## Miscellaneous

### Too many format args (E1305) [](#E1305)

This error occurs when we use the `format` method on a string, but call it with more arguments than
the number of `{}` in the string.

```{literalinclude} /../examples/pylint/E1305_too_many_format_args.py
```

Corrected version:

```python
name = "Amy"
age = "17"
country = "England"

s = "{} who is {} lives in {}".format(name, age, country)
```

**See also**: [E1121](#E1121)

### Too few format args (E1306) [](#E1306)

This error occurs when we use the `format` method on a string, but call it with fewer arguments than
the number of `{}` in the string.

```{literalinclude} /../examples/pylint/E1306_too_few_format_args.py
```

Corrected version:

```python
s = "{} and {}".format("first", "second")
```

**See also**: [E1120](#E1120)

### Missing format argument key (W1303) [](#W1303)

This error occurs when a format string that uses named fields does not receive the required
keywords. In the following example, we should assign three values for `last_name`, `first_name`,
and `age`.

```{literalinclude} /../examples/pylint/W1303_missing_format_argument_key.py
```

Corrected version:

```python
s = '{last_name}, {fist_name} - {age}'.format(last_name='bond', first_name='james', age=37)
```

**See also**: [E1120](#E1120), [E1306](#E1120)

### Bad str strip call (E1310) [](#E1310)

This error occurs when we call [`strip`][str.strip], [`lstrip`][str.lstrip],
or [`rstrip`][str.rstrip], but pass an argument string which contains duplicate characters. The
argument string should contain the *distinct* characters that we want to remove from the end(s) of a
string.

```{literalinclude} /../examples/pylint/E1310_bad_str_strip_call.py
```

It is a common mistake to think that `mystring.strip(chars)` removes the substring `chars` from the
beginning and end of `mystring`. It actually removes all characters in `chars` from the beginning
and end of `mystring`, *irrespective of their order*! If we pass an argument string with duplicate
characters to `mystring.strip`, we are likely misinterpreting what this method is doing.

### Format combined specification (W1305) [](#W1305)

This error occurs when a format string contains both automatic field numbering (e.g. `{}`) and
manual field specification (e.g. `{0}`).

For example, we should not use `{}` and `{index}` at the same time.

```{literalinclude} /../examples/pylint/W1305_format_combined_specification.py
```

Corrected version:

```python
s = "{} and {}".format("a", "b")
```

or:

```python
s = "{0} and {1}".format("a", "b")
```

### Anomalous backslash in string (W1401) [](#W1401)

This error occurs when a string literal contains a backslash that is not part of an escape sequence.

```{literalinclude} /../examples/pylint/W1401_anomalous_backslash_in_string.py
```

The following is a [list of recognized escape sequences][String and Bytes literals] in Python string
literals.

```
\newline    \a          \r          \xhh
\\          \b          \t          \N{name}
\'          \f          \v          \uxxxx
\"          \n          \ooo        \Uxxxxxxxx
```

If a backslash character is not used to start one of the escape sequences listed above, we should
make this explicit by escaping the backslash with another backslash.

```python
print('This is a tab: \t')
print('This is a newline: \n')
print('This is not an escape sequence: \\d')
```

### Redundant unittest assert (W1503) [](#W1503)

The first argument of `assertTrue` and `assertFalse` is a "condition", which should evaluate
to `True` or `False`. These methods evaluate the condition to check whether the test passes or
fails. The conditions should depend on the code that we are testing, and should not be a constant
literal like `True` or `4`. Otherwise, the test will always have the same result, regardless of
whether our code is correct.

```{literalinclude} /../examples/pylint/W1503_redundant_unittest_assert.py
```

### Unidiomatic type check (C0123) [](#C0123)

This error occurs when `type` is used instead of `isinstance` to perform a type check.
Use `isinstance(x, Y)` instead of `type(x) == Y`.

```{literalinclude} /../examples/pylint/C0123_unidiomatic_typecheck.py
```

The above can be modified to:

```python
def is_int(obj: Union[int, float, str]) -> bool:
    """Check if the given object is of type 'int'."""
    return isinstance(obj, int)
```

**See also**: [C0121](#C0121)

### Dangerous default value (W0102) [](#W0102)

This warning occurs when a mutable object, such as a list or dictionary, is provided as a default
argument in a function definition. Default arguments are instantiated only once, at the time when
the function is defined (i.e. when the interpreter encounters the `def ...` block). If the default
argument is mutated when the function is called, it will remain modified for all subsequent function
calls. This leads to a common "gotcha" in Python, where an "empty" list or dictionary, specified as
the default argument, starts containing values on calls other than the first call.

```{literalinclude} /../examples/pylint/W0102_dangerous_default_value.py
```

Many new users of Python would expect the output of the code above to be:

```python
[0, 1, 2, 3, 4]
[0, 1, 2, 3, 4]
```

However, the actual output is:

```python
[0, 1, 2, 3, 4]
[0, 1, 2, 3, 4, 0, 1, 2, 3, 4]
```

If we want to prevent this surprising behavior, we should use `None` as the default argument, and
then check for `None` inside the function body. For example, the following code prints the expected
output:

```python
from typing import List, Optional

def make_list(n: int, lst: Optional[List[int]]=None) -> List[int]:
    if lst is None:
        lst = []
    for i in range(n):
        lst.append(i)
    return lst


print(make_list(5))
print(make_list(5))
```

**See also**:

- [Common Gotchas - Mutable Default Arguments]
- [Default Parameter Values in Python]

### Consider iterating dictionary (C0201) [](#C0201)

It is more *pythonic* to iterate through a dictionary directly, without calling the `.keys` method.

```{literalinclude} /../examples/pylint/C0201_consider_iterating_dictionary.py
```

Corrected version:

```python
for item in menu:
    print("My store sells {}.".format(item))
```

### Superfluous parens (C0325) [](#C0325)

This error occurs when a keyword, such as `if` or `for`, is followed by a single item enclosed in
parentheses. In such a case, parentheses are not necessary.

```{literalinclude} /../examples/pylint/C0325_superfluous_parens.py
```

Corrected version:

```python
if 'anchovies' in pizza_toppings:
    print("Awesome!")
```

### Trailing comma tuple (R1707) [](#R1707)

This error occurs when a Python expression is terminated by a comma. In Python, a tuple is created
by the comma symbol, not by parentheses. This makes it easy to create a tuple accidentally, by
misplacing a comma, which can lead to obscure bugs. In order to make our intention clear, we should
always use parentheses when creating a tuple, and we should never leave a trailing comma in our
code.

```{literalinclude} /../examples/pylint/R1707_trailing_comma_tuple.py
```

Corrected version:

```python
my_lucky_number = 7
print(my_lucky_number)  # Prints 7
```

### Assert on tuple (W0199) [](#W0199)

This error occurs when an `assert` statement is called with a tuple as the first argument. `assert`
acting on a tuple passes if and only if the tuple is non-empty. This is likely *not* what the
programmer had intended.

```{literalinclude} /../examples/pylint/W0199_assert_on_tuple.py
```

If we would like to assert multiple conditions, we should join those conditions using the `and`
operator, or use individual `assert` statements for each condition.

```python
def check(condition1: bool, condition2: bool, condition3: bool) -> None:
    # Option 1
    assert (condition1 and condition2 and condition3)
    # Option 2
    assert condition1
    assert condition2
    assert condition3
```

If we would like `assert` to show a special error message when the assertion fails, we should
provide that message as the second argument.

```python
def check(condition, message):
    assert condition, message  # the message is optional
```

### Literal comparison (R0123) [](#R0123)

This error occurs when we use the identity operator `is` to compare non-boolean Python literals.
Whether or not two literals representing the same value (e.g. two identical strings) have the same
identity can vary, depending on the way the code is being executed, the code that has ran
previously, and the version and implementation of the Python interpreter. For example, each of the
following assertions pass if the lines are evaluated together from a Python file,
but `assert num is 257` and `assert chars is 'this string fails'` fail if the lines are entered into
a Python interpreter one-by-one.

```{literalinclude} /../examples/pylint/R0123_literal_comparison.py
```

To prevent the confusion, it is advisable to use the equality operator `==` when comparing objects
with Python literals.

```python
num = 256
assert num == 256

num = 257
assert num == 257

chars = 'this_string_passes'
assert chars == 'this_string_passes'

chars = 'this string fails'
assert chars == 'this string fails'
```

**See also**:

- [Literally Literals and Other Number Oddities In Python]
- [StackOverflow: About the changing id of an immutable string]
- [StackOverflow: When does Python allocate new memory for identical strings?]

### Expression not assigned (W0106) [](#W0106)

This error occurs when an expression that is not a function call is not assigned to a variable.
Typically, this indicates that we were intending to do something else.

```{literalinclude} /../examples/pylint/W0106_expression_not_assigned.py
```

Corrected version:

```python
lst = [1, 2, 3]
lst.append(4)
print("Appended 4 to my list!")
```

### Invalid length returned (E0303) [](#E0303)

This error occurs when the `__len__` special method returns something other than a non-negative
integer.

```{literalinclude} /../examples/pylint/E0303_invalid_length_returned.py
```

Corrected version:

```python
class Company:
    """A company with some employees."""

    def __init__(self, employees: List[str]) -> None:
        self._employees = employees

    def __len__(self) -> int:
        return len(self._employees)
```

## Style errors [](#style)

### Multiple statements (C0321) [](#C0321)

This error occurs when we write more than one statement on a single line. According to PEP8, [*
multiple statements on the same line are discouraged*][PEP8: Other Recommendations].

```{literalinclude} /../examples/pylint/C0321_multiple_statements.py
```

Corrected version:

```python
def is_positive(number: int) -> str:
    """Return whether the number is 'positive' or 'negative'."""
    if number > 0:
        return 'positive'
    else:
        return 'negative'
```

### Unnecessary semicolon (W0301) [](#W0301)

This error occurs when we end a Python statement with a semicolon. There is no good reason to ever
use a semicolon in Python.

```{literalinclude} /../examples/pylint/W0301_unnecessary_semicolon.py
```

Corrected version:

```python
print("Hello World!")
```

### Missing final newline (C0304) [](#C0304)

This error occurs when a file is missing a trailing newline character. For example, if we represent
a (typically invisible) newline character as `¬`, the following file would raise this error:

```{literalinclude} /../examples/pylint/C0304_missing_final_newline.py
```

while the corrected file which contains a trailing newline character would not:

```python
print("Hello World!")  # Trailing newline is present:  ¬
```

### Trailing newlines (C0305) [](#C0305)

This error occurs when a file ends with more than one newline character (i.e. when a file contains
trailing blank lines). For example:

```{literalinclude} /../examples/pylint/C0305_trailing_newlines.py
```

Corrected version:

```python
print("Hello World!")  # This file ends with a single newline character! :)
```

### Line too long (C0301) [](#C0301)

This error occurs when a line is longer than a predefined number of characters. Our default limit
for all lines is 80 characters.

```{literalinclude} /../examples/pylint/C0301_line_too_long.py
```

## Syntax errors

### Syntax Error (E0001) [](#E0001)

1. *SyntaxError: Missing parentheses in call to 'print'*

   In Python 3, `print` is a builtin *function*, and should be called like any other function, with
   arguments inside parentheses. In previous versions of Python, `print` had been a keyword.

    ```{literalinclude} /../examples/syntax_errors/missing_parentheses_in_call_to_print.py
    ```

2. *SyntaxError: can't assign to literal*

   There must always be a variable on the left-hand side of the equals sign (where the term "
   variable" can refer to a single identifier `a = 10`, multiple identifiers `a, b = 10, 20`, a
   dictionary element `foo['a'] = 10`, a class attribute `foo.bar = 10`, etc.). We cannot assign to
   a string or numeric literal.

    ```{literalinclude} /../examples/syntax_errors/assignment_to_literal.py
    ```

3. *SyntaxError: invalid syntax*

   Some of the common causes of this error include:

    1. Missing colon at the end of an `if`, `elif`, `else`, `for`, `while`, `class`, or `def`
       statement.

        ```{literalinclude} /../examples/syntax_errors/missing_colon.py
        ```
  
    2. Assignment operator `=` used inside a condition expression (likely in place of the equality
       operator `==`).

        ```{literalinclude} /../examples/syntax_errors/assignment_inside_condition.py
        ```

    3. Missing quotation mark at the beginning or the end of a string literal.

        ```{literalinclude} /../examples/syntax_errors/missing_quote.py
        ```

    4. Assignment to a Python keyword.

        ```{literalinclude} /../examples/syntax_errors/assignment_to_keyword.py
        ```

       The following is a [list of Python keywords][Keywords] which cannot be used as variable
       names:

       ```
       False      class      finally    is         return
       None       continue   for        lambda     try
       True       def        from       nonlocal   while
       and        del        global     not        with
       as         elif       if         or         yield
       assert     else       import     pass
       break      except     in         raise
       ```

    5. Use of an undefined operator. For example, there are no "increment by one" `++` or "decrement
       by one" `--` operators in Python.

      ```{literalinclude} /../examples/syntax_errors/undefined_operator.py
      ```

4. *IndentationError: unindent does not match any outer indentation level*

   We must use a constant number of whitespace characters for each level of indentation. If we start
   a code block using four spaces for indentation, we must use four spaces throughout that code
   block.

    ```{literalinclude} /../examples/syntax_errors/unindent_does_not_match_indentation.py
    ```

   Note that it is **strongly recommended** that we [**always use four spaces per indentation
   level**][PEP8: Indentation] throughout our code.

5. *IndentationError: unexpected indent*

   In Python, the only time we would increase the indentation level of our code is to define a new
   code block after a [compound statement][Compound statements] such as `for`, `if`, `def`,
   or `class`.

    ```{literalinclude} /../examples/syntax_errors/unexpected_indent.py
    ```

### Nonexistent operator (E0107) [](#E0107)

This error occurs when we attempt to use C-style "pre-increment" or "pre-decrement" operators `++`
and `--`, which do not exist in Python.

```{literalinclude} /../examples/pylint/E0107_nonexistent_operator.py
```

Corrected version:

```python
spam = 0
spam += 1
spam -= 1
```

## Older errors

The following errors are no longer checked by the latest version of PythonTA.

### Bad whitespace (C0326) [](#C0326)

This error occurs when we include a wrong number of spaces around an operator, bracket, or block
opener. We should aim to follow
the [PEP8 convention on whitespace in expressions and statements][PEP8: Whitespace in Expressions and Statements]
.

### Bad indentation (W0311) [](#W0311)

This error occurs when an unexpected number of tabs or spaces is used to indent the code. It is
recommended that we use [*four spaces per indentation level*][PEP8: Indentation] throughout our
code.

### Mixed indentation (W0312) [](#W0312)

This error occurs when the code is indented with a mix of tabs and spaces. Please note that [*spaces
are the preferred indentation method*][PEP8: Tabs or Spaces?].

### Bad continuation (C0330) [](#C0330)

This error occurs when we use an inconsistent number of spaces to indent arguments or parameters in
function and method calls or definitions.


<!-- Python objects -->

[`__init__`]: https://docs.python.org/3/reference/datamodel.html#object.__init__

[`__new__`]: https://docs.python.org/3/reference/datamodel.html#object.__init__

[str.strip]: https://docs.python.org/3/library/stdtypes.html#str.strip

[str.lstrip]: https://docs.python.org/3/library/stdtypes.html#str.lstrip

[str.rstrip]: https://docs.python.org/3/library/stdtypes.html#str.rstrip

[super]: https://docs.python.org/3/library/functions.html#super

[`input`]: https://docs.python.org/3/library/functions.html#input

[`open`]: https://docs.python.org/3/library/functions.html#open

[`print`]: https://docs.python.org/3/library/functions.html#print

<!-- Python docs -->

[`math` module]: https://docs.python.org/3/library/math.html

[`pass` statements]: https://docs.python.org/3/tutorial/controlflow.html#pass-statements

[AttributeError]: https://docs.python.org/3/library/exceptions.html#AttributeError

[Binary arithmetic operations]: https://docs.python.org/3/reference/expressions.html#binary-arithmetic-operations

[Built-in Functions]: https://docs.python.org/3/library/functions.html

[Compound statements]: https://docs.python.org/3/reference/compound_stmts.html

[Keywords]: https://docs.python.org/3/reference/lexical_analysis.html#keywords

[Python Documentation: BaseException]: https://docs.python.org/3/library/exceptions.html#BaseException

[Python Documentation: decorator]: https://docs.python.org/3/glossary.html#term-decorator

[Python Documentation: Exception]: https://docs.python.org/3/library/exceptions.html#Exception

[Python Documentation: iterable]: https://docs.python.org/3/glossary.html#term-iterable

[Python Documentation: KeyboardInterrupt]: https://docs.python.org/3/library/exceptions.html#KeyboardInterrupt

[Python Documentation: NotImplemented]:https://docs.python.org/3/library/constants.html#NotImplemented

[Python Documentation: NotImplementedError]:https://docs.python.org/3/library/constants.html#NotImplementedError

[Python Documentation: staticmethod]: https://docs.python.org/3/library/functions.html#staticmethod

[String and Bytes literals]: https://docs.python.org/3/reference/lexical_analysis.html#string-and-bytes-literals

[Unary arithmetic and bitwise operations]: https://docs.python.org/3/reference/expressions.html#unary-arithmetic-and-bitwise-operations

<!-- PEP8 -->

[PEP8 Imports]: https://www.python.org/dev/peps/pep-0008/#imports

[PEP8: Indentation]: https://www.python.org/dev/peps/pep-0008/#indentation

[PEP8: Naming Conventions]: https://www.python.org/dev/peps/pep-0008/#naming-conventions

[PEP8: Other Recommendations]: https://www.python.org/dev/peps/pep-0008/#other-recommendations

[PEP8: Tabs or Spaces?]: https://www.python.org/dev/peps/pep-0008/#tabs-or-spaces

[PEP8: Whitespace in Expressions and Statements]: https://www.python.org/dev/peps/pep-0008/#whitespace-in-expressions-and-statements

<!-- StackOverflow -->

[StackOverflow: About the changing id of an immutable string]: https://stackoverflow.com/questions/24245324/about-the-changing-id-of-an-immutable-string

[StackOverflow: How To Use The Pass Statement In Python]: https://stackoverflow.com/a/22612774/2063031

[StackOverflow: What does 'super' do in Python?]: https://stackoverflow.com/q/222877/2063031

[StackOverflow: What is the difference between `@staticmethod` and `@classmethod` in Python?]: https://stackoverflow.com/questions/136097/what-is-the-difference-between-staticmethod-and-classmethod-in-python

[StackOverflow: When does Python allocate new memory for identical strings?]: https://stackoverflow.com/questions/2123925/when-does-python-allocate-new-memory-for-identical-strings

<!-- everything else -->

[Common Gotchas - Mutable Default Arguments]: http://docs.python-guide.org/en/latest/writing/gotchas/#mutable-default-arguments

[Default Parameter Values in Python]: http://effbot.org/zone/default-values.htm

[list comprehensions tutorial]: https://www.digitalocean.com/community/tutorials/understanding-list-comprehensions-in-python-3

[Literally Literals and Other Number Oddities In Python]: https://www.everymundo.com/literals-other-number-oddities-python/

[Python double-under, double-wonder]: https://www.pixelmonkey.org/2013/04/11/python-double-under-double-wonder

[Python's Super Considered Harmful]: https://fuhm.net/super-harmful/

[Super Considered Super!]: https://youtu.be/EiOglTERPEo

[The scope of index variables in Python's for loops]: http://eli.thegreenplace.net/2015/the-scope-of-index-variables-in-pythons-for-loops/

[The story of None, True and False]: http://python-history.blogspot.ca/2013/11/story-of-none-true-false.html

[Global Variables Are Bad]: https://wiki.c2.com/?GlobalVariablesAreBad
