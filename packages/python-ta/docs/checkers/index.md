# PythonTA Checks

This page describes in greater detail the errors that PythonTA checks for.
If anything is unclear, incorrect, or missing, please don't hesitate to send an
email to \[david at cs dot toronto dot edu\].

## Improper Python usage

These errors generally indicate a misuse of variables, control flow, or other Python features in our
code.

(E0601)=

### Used before assignment (E0601)

This error occurs when we are using a variable before it has been assigned a value.

```{literalinclude} /../../../examples/pylint/e0601_used_before_assignment.py

```

(E0602)=

### Undefined variable (E0602)

This error occurs when we are using a variable that has not been defined.

```{literalinclude} /../../../examples/pylint/e0602_undefined_variable.py

```

(W0631)=

### Undefined loop variable (W0631)

This error occurs when a loop variable is used outside the `for` loop where it was defined.

```{literalinclude} /../../../examples/pylint/w0631_undefined_loop_variable.py

```

Python, unlike many other languages (e.g. C, C++, Java), allows loop variables to be accessed
outside the loop in which they were defined. However, this practice is discouraged, as it can lead
to obscure and hard-to-detect bugs.

**See also**:

- [The scope of index variables in Python's for loops]

(E0103)=

### Not in loop (E0103)

This error occurs when the `break` or `continue` keyword is used outside of a loop. The
keyword `break` is used to exit a loop early and the keyword `continue` is used to skip an iteration
in a loop. Hence, both keywords only belong inside loops.

```{literalinclude} /../../../examples/pylint/e0103_not_in_loop.py

```

A common source of this error is when the `break` or `continue` is not indented properly (it must be
indented to be considered part of the loop body).

(E0104)=

### Return outside function (E0104)

This error occurs when a `return` statement is found outside a function or method.

```{literalinclude} /../../../examples/pylint/e0104_return_outside_function.py

```

A common source of this error is when the `return` is not indented properly (it must be indented to
be considered part of the loop body).

(E0643)=

### Potential index error (E0643)

This error occurs when trying to access the index of an iterable (such as `list`, `str`, or `tuple`) that's beyond its length.

```{literalinclude} /../../../examples/pylint/e0643_potential_index_error.py

```

Corrected Version:

```python
coffees = ['americano', 'latte', 'macchiato', 'mocha']
print(coffees[3])
```

(W0101)=

### Unreachable (W0101)

This error occurs when there is some code after a `return` or `raise` statement. This code will
never be run, so either it should be removed, or the function is returning too early.

```{literalinclude} /../../../examples/pylint/w0101_unreachable.py

```

(W0109)=

### Duplicate key (W0109)

This error occurs when a dictionary literal sets the same key multiple times.

```{literalinclude} /../../../examples/pylint/w0109_duplicate_key.py

```

Dictionaries map unique keys to values. When different values are assigned to the same key, the last
assignment takes precedence. This is rarely what the user wants when they are constructing a
dictionary.

(W0130)=

### Duplicate Value (W0130)

This error occurs when a set literal contains the same value two or more times.

```{literalinclude} /../../../examples/pylint/w0130_duplicate_value.py

```

Corrected version:

```python
correct_set = {'value 1', 2, 3}
```

Sets are unordered and duplicate elements are not allowed.

(E1123)=

### Unexpected keyword arg (E1123)

This error occurs when a function call passes a keyword argument which does not match the signature
of the function being called.

```{literalinclude} /../../../examples/pylint/e1123_unexpected_keyword_arg.py

```

Corrected version:

```python
print_greeting(name="Arthur")
```

## Type errors

These errors are some of the most common errors we encounter in Python. They generally have to do
with using a value of one type where another type is required.

(E1101)=

### No member (E1101)

This error occurs when we use dot notation (`my_var.x`) to access an attribute or to call a method
which does not exist for the given object. This can happen both for built-in types like `str` and
for classes that we define ourselves. This error often results in
an [`AttributeError`][attributeerror] when we run the code.

```{literalinclude} /../../../examples/pylint/e1101_no_member.py

```

(E1102)=

### Not callable (E1102)

This error occurs when we try to call a value which is not a function, method, or callable object.
In the following example, we should not call `x()` because `x` refers to an integer, and calling an
integer has no meaning.

```{literalinclude} /../../../examples/pylint/e1102_not_callable.py

```

(E1111)=

### Assignment from no return (E1111)

This error occurs when we assign a variable to the return value of a function call, but the function
never returns anything. In the following example, `add_fruit` mutates `fruit_basket` instead of
returning a new list. As a result, `new_fruit_basket` always gets the value `None`.

```{literalinclude} /../../../examples/pylint/e1111_assignment_from_no_return.py

```

We should either modify `add_fruit` to return a new list, or call `add_fruit` without assigning the
return value to a variable.

(E1128)=

### Assignment from None (E1128)

This error occurs when we assign a variable the return value of a function call, but the function
always returns `None`. In the following example, `add_fruit` always returns `None`. As a
result, `new_fruit_basket` will always get the value `None`.

```{literalinclude} /../../../examples/pylint/e1128_assignment_from_none.py

```

(E1120)=

### No value for parameter (E1120)

A function must be called with one argument value per parameter in its header. This error indicates
that we called a function with too few arguments. In the following example, there should be _three_
values passed to the function instead of two.

```{literalinclude} /../../../examples/pylint/e1120_no_value_for_parameter.py

```

Corrected version:

```python
get_sum(1, 2, 3)
```

(E1121)=

### Too many function args (E1121)

A function must be called with one argument value per parameter in its header. This error indicates
that we called a function with too many arguments. In the following example, there should be _two_
values passed to the function instead of three.

```{literalinclude} /../../../examples/pylint/e1121_too_many_function_args.py

```

Corrected version:

```python
get_sum(1, 2)
```

(W1117)=

### Keyword argument superseded by positional argument (W1117)

This error occurs when a function is called with keyword arguments with the same name as positional-only parameters and the function contains a keyword variadic parameter dict.

In the example below, `greeting` is a positional-only parameter of the function `print_greeting`.
However, when the function is called, `"Hi"` is passed as a keyword argument. As a result, it will be collected in a dictionary by the keyword variadic parameter `kwds`,
and the function will print out the default value `"Hello"`, which is an unintended behavior of the function call.

```{literalinclude} /../../../examples/pylint/w1117_kwarg_superseded_by_positional_arg.py

```

Corrected version:

```python
print_greeting("Hi")
```

This will print out `"Hi"` as intended.

(E1126)=

### Invalid sequence index (E1126)

This error occurs when a list or tuple is indexed using the square bracket notation `my_list[...]`,
but the value of the index is not an integer.

Remember that the index indicates the _position_ of the item in the list/tuple.

```{literalinclude} /../../../examples/pylint/e1126_invalid_sequence_index.py

```

Corrected version:

```python
a = ['p', 'y', 'T', 'A']
print(a[0])
```

(E1127)=

### Invalid slice index (E1127)

This error occurs when a list or tuple is sliced using the square bracket
notation `my_list[... : ...]`, but the two values on the left and right of the colon are not
integers.

Remember that the slice numbers indicate the _start_ and _stop_ positions for the slice in the
list/tuple.

```{literalinclude} /../../../examples/pylint/e1127_invalid_slice_index.py

```

Corrected version:

```python
a = ['p', 'y', 'T', 'A']
print(a[0:3])
```

(E1130)=

### Invalid unary operand type (E1130)

This error occurs when we use a [unary operator][unary arithmetic and bitwise operations] (`+`, `-`
, `~`) on an object which does not support this operator. For example, a list does not support
negation.

```{literalinclude} /../../../examples/pylint/e1130_invalid_unary_operand_type.py

```

(E1131)=

### Unsupported binary operation (E1131)

This error occurs when we use a [binary arithmetic operator][binary arithmetic operations] like `+`
or `*`, but the left and right sides are not compatible types. For example, a dictionary cannot be
added to a list.

```{literalinclude} /../../../examples/pylint/e1131_unsupported_binary_operation.py

```

(E1135)=

### Unsupported membership test (E1135)

This error occurs when we use the membership test `a in b`, but the type of `b` does not support
membership tests.

The standard Python types which support membership tests are strings, lists, tuples, and
dictionaries.

```{literalinclude} /../../../examples/pylint/e1135_unsupported_membership_test.py

```

(E1136)=

### Unsubscriptable object (E1136)

This error occurs when we try to index a value using square brackets (`a[...]`), but the type of `a`
does not support indexing (or "subscripting").

The standard Python types which support indexing are strings, lists, tuples, and dictionaries.

```{literalinclude} /../../../examples/pylint/e1136_unsubscriptable_object.py

```

(E1137)=

### Unsupported assignment operation (E1137)

This error occurs when we assign something to an object which does not support assignment (i.e. an
object which does not define the `__setitem__` method).

```{literalinclude} /../../../examples/pylint/e1137_unsupported_assignment_operation.py

```

(E1138)=

### Unsupported delete operation (E1138)

This error occurs when the `del` keyword is used to delete an item from an object which does not
support item deletion (i.e. an object that does not define the `__delitem__` special method).

```{literalinclude} /../../../examples/pylint/e1138_unsupported_delete_operation.py

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

(E1144)=

### Invalid Slice Step (E1144)

This error occurs when a slice step is 0.

```{literalinclude} /../../../examples/pylint/e1144_invalid_slice_step.py

```

(E0632)=

### Unbalanced tuple unpacking (E0632)

This error occurs when we are trying to assign to multiple variables at once, but the right side has
too few or too many values in the sequence.

```{literalinclude} /../../../examples/pylint/e0632_unbalanced_tuple_unpacking.py

```

(W0644)=

### Unbalanced dict unpacking (W0644)

This error occurs when we are trying to assign dictionary keys or values to multiple variables at
once, but the right side has too few or too many values.

```{literalinclude} /../../../examples/pylint/w0644_unbalanced_dict_unpacking.py

```

Corrected version:

```python
SCORES = {
    "bob": (1, 1, 3, 2),
    "joe": (4, 3, 1, 2),
    "billy": (2, 2, 2, 2),
}

a, b, c = SCORES  # unpacking the dictionary keys

for d, e, f in SCORES.values():  # unpacking the dictionary values
    print(d)
```

Note that when using unpacking with a dictionary on the right-hand side of an `=`, the variables on the left-hand side gets assigned the keys of the dictionary. For example,

```python
test = {
  "hi": 0,
  "bye": 1,
}

# `a` gets assigned "hi", `b` gets assigned "bye"
a, b = test
```

(E0633)=

### Unpacking non-sequence (E0633)

This error occurs when we are trying to assign to multiple variables at once, but the right side is
not a sequence, and so can't be unpacked.

```{literalinclude} /../../../examples/pylint/e0633_unpacking_non_sequence.py

```

(E1133)=

### Not an iterable (E1133)

This error occurs when a non-iterable value is used in a place where an iterable is expected.
An [iterable][python documentation: iterable] is an object capable of returning its members one at a
time. Examples of iterables include sequence types such as `list`, `str`, and `tuple`, some
non-sequence types such as `dict`, and instances of other classes which define the `__iter__`
or `__getitem__` special methods.

```{literalinclude} /../../../examples/pylint/e1133_not_an_iterable.py

```

Corrected version:

```python
for number in [1, 2, 3]:
    print(number)
```

(E1134)=

### Not a mapping (E1134)

This error occurs when a non-mapping value is used in a place where mapping is expected. This is a result of unpacking a non-dict with `**` in a function call meaning that the parameters are unfilled.

`**` can only be used on a `dict` to unpack the values.

```{literalinclude} /../../../examples/pylint/e1134_not_a_mapping.py

```

## Code complexity

(C0117)=

### Unnecessary negation (C0117)

This error occurs when a boolean expression contains an unnecessary negation. If we are getting this
error, the expression can be simplified to not use a negation.

```{literalinclude} /../../../examples/pylint/c0117_unnecessary_negation.py

```

The above can be modified to:

```python
number = 5
if number < 0:
    number_category = 'negative'
else:
    number_category = 'non-negative'
```

(C0209)=

### Consider using f-string (C0209)

This error occurs when a string is formatted with `%` or `format()`.
The preferred way to include Python values in strings is with f-strings.

```{literalinclude} /../../../examples/pylint/c0209_consider_using_f_string.py

```

The above can be changed to:

```python
name = "Bob"
print(f"Hi! My name is {name}!")
print(f"{name} is my name!")
```

(R1726)=

### Simplifiable condition (R1726)

This error occurs when a boolean test condition can be simplified.
Test conditions are expressions evaluated inside of statements such as `if`, `while`, or `assert`.

```{literalinclude} /../../../examples/pylint/r1726_simplifiable_condition.py

```

The above can be modified to:

```python
if a:  # Error was on this line
  pass
```

(R1727)=

### Condition evals to constant (R1727)

This error occurs when a boolean test condition always evaluates to a constant.
Test conditions are expressions evaluated inside of statements such as `if`, `while`, or `assert`.

```{literalinclude} /../../../examples/pylint/r1727_condition_evals_to_constant.py

```

The above can be modified to:

```python
if True:  # Error was on this line
  pass
```

(C0121)=

### Singleton comparison (C0121)

This error occurs when an expression is compared to a singleton value like `True`, `False` or `None`
.

Here is an example involving a comparison to `None`:

```{literalinclude} /../../../examples/pylint/c0121_singleton_comparison.py

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

- [The story of None, True and False (and an explanation of literals, keywords and builtins thrown in)][the story of none, true and false]

(W0125)=

### Using constant test (W0125)

This error occurs when a conditional statement (like an `if` statement) uses a constant value for
its test. In such a case, a conditional statement is not necessary, as it will always result in the
same path of execution.

```{literalinclude} /../../../examples/pylint/w0125_using_constant_test.py

```

(W0128)=

### Redeclared Assigned Name (W0128)

This error occurs when a variable is redeclared on the same line it was assigned.

```{literalinclude} /../../../examples/pylint/w0128_redeclared_assigned_name.py

```

(R0912)=

### Too many branches (R0912)

The function or method has too many branches, making it hard to follow. This is a sign that the
function/method is too complex, and should be split up.

**Note**: The checker limit is 12 branches.

```{literalinclude} /../../../examples/pylint/r0912_too_many_branches.py

```

(R1702)=

### Too many nested blocks (R1702)

This error occurs when we have more than three levels of nested blocks in our code. Deep nesting is
a sign that our function or method is too complex, and should be broken down using helper functions
or rewritten as a [list comprehension][list comprehensions tutorial].

**Note**: This checker does not count function, method, or class definitions as blocks, so the
example below is considered to have _six_ nested blocks, not seven.

```{literalinclude} /../../../examples/pylint/r1702_too_many_nested_blocks.py

```

The code above can be fixed using a helper function:

```python
def drop_none(lst: list[Optional[int]]) -> list[int]:
    """Return a copy of `lst` with all `None` elements removed."""
    new_lst = []
    for element in lst:
        if element is not None:
            new_lst.append(element)
    return new_lst


def cross_join(x_list: list[Optional[int]], y_list: list[Optional[int]],
               z_list: list[Optional[int]]) -> list[tuple[int, int, int]]:
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
def cross_join(x_list: list[Optional[int]], y_list: list[Optional[int]],
               z_list: list[Optional[int]]) -> list[tuple[int, int, int]]:
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

(C0302)=

### Too many lines (C0302)

This error occurs when the file has too many lines. The limit for too many lines is specified
through the `max-module-lines` configuration option.

**Note**: The default value is `1000`.

(R0913)=

### Too many arguments (R0913)

The function or method is defined with too many arguments. This is a sign that the function/method
is too complex, and should be split up, or that some of the arguments are related, and should be
combined and passed as a single object.

**Note**: The checker limit is 5 arguments.

```{literalinclude} /../../../examples/pylint/r0913_too_many_arguments.py

```

(R0914)=

### Too many locals (R0914)

The function or method has too many local variables.

**Note**: The checker limit is 15 local variables.

```{literalinclude} /../../../examples/pylint/r0914_too_many_locals.py

```

(R0915)=

### Too many statements (R0915)

The function or method has too many statements. We should split it into smaller functions/methods.

**Note**:

- The checker limit is 50 statements.
- Comments do not count as statements.

```{literalinclude} /../../../examples/pylint/r0915_too_many_statements.py

```

(W0612)=

### Unused variable (W0612)

This error occurs when we have a defined variable that is never used.

```{literalinclude} /../../../examples/pylint/w0612_unused_variable.py

```

(W0613)=

### Unused argument (W0613)

This error occurs when a function argument is never used in the function.

```{literalinclude} /../../../examples/pylint/w0613_unused_argument.py

```

(W0104)=

### Pointless statement (W0104)

This error occurs when a statement does not have any effect. This means that the statement could be
removed without changing the behaviour of the program.

```{literalinclude} /../../../examples/pylint/w0104_pointless_statement.py

```

(W0105)=

### Pointless string statement (W0105)

This error occurs when a string statement does not have any effect. Very similar to error `W0104`, but
for strings.

```{literalinclude} /../../../examples/pylint/w0105_pointless_string_statement.py

```

(R1733)=

### Unnecessary dict index lookup (R1733)

This error occurs when values for a dictionary are accessed using an index lookup (that is, through
`dictionary_name[key]`) instead of directly while iterating over key-value pairs of the dictionary.

```{literalinclude} /../../../examples/pylint/r1733_unnecessary_dict_index_lookup.py

```

The code above can be fixed by accessing the dictionary values directly:

```python
sample_dict = {"key_one": "value_one", "key_two": "value_two"}

for key, value in sample_dict.items():
    print(key, value)  # Direct access instead of an index lookup
```

(R1736)=

### Unnecessary list index lookup (R1736)

This error occurs when iterating through a list while keeping track of both index and value using `enumerate()` but still using the index to access the value (which can be accessed directly).

```{literalinclude} /../../../examples/pylint/r1736_unnecessary_list_index_lookup.py

```

Corrected version:

```python
colours = ['red', 'blue', 'yellow', 'green']

for index, colour in enumerate(colours):
    print(index)
    print(colour)
```

(W0107)=

### Unnecessary pass (W0107)

This error occurs when a [`pass` statement][`pass` statements] is used that can be avoided (or has
no effect). `pass` statements should only be used to fill what would otherwise be an empty code
block, since code blocks cannot be empty in Python.

```{literalinclude} /../../../examples/pylint/w0107_unnecessary_pass.py

```

In the above example, the `pass` statement is "unnecessary" as the program's effect is not changed
if `pass` is removed.

**See also:**

- [StackOverflow: How To Use The Pass Statement In Python]

(W2301)=

### Unnecessary ellipsis (W2301)

This error occurs when a docstring is the preceding line of an ellipsis or if there is a statement
in the same scope as an ellipsis. An ellipsis should only be used as a "placeholder" to fill in a block
of code that requires at least one statement.

```{literalinclude} /../../../examples/pylint/w2301_unnecessary_ellipsis.py

```

Corrected version:

```python
def my_func() -> None:
    """Test Doctest"""
    if True:
        ...
```

(R9710)=

### Inconsistent returns (R9710)

This error occurs when you have a function that sometimes has return statements with
non-`None` values and sometimes has only `return`. This is an issue because in Python, we prefer making code explicit
rather than implicit. This error replaces pylint's [R1710](https://pylint.pycqa.org/en/latest/user_guide/messages/refactor/inconsistent-return-statements.html).

```{literalinclude} /../../../examples/custom_checkers/r9710_inconsistent_returns.py

```

In `add_sqrts`, we should change `return` into `return None` to make better contrast the return
value with the other branch. In the other two functions, it's possible that none of the `return`
statements will execute, and so the end of the function body will be reached, causing a `None` to be
returned implicitly.
(Forgetting about this behaviour actually is a common source of bugs in student code!)
In both cases, you can fix the problem by adding an explicit `return None` to the end of the
function body.

In CSC148, you may sometimes choose resolve this error by instead _raising an error_ rather than
returning `None`.

(R9711)=

### Missing return statement (R9711)

This error occurs when a function is missing return statements in at least one branch, when the function's return type annotation is not "None".

```{literalinclude} /../../../examples/custom_checkers/r9711_missing_return_statement.py

```

(R1732)=

### Consider using with (R1732)

This error occurs when a resource allocating operation such as opening a file can be replaced by a `with` block. By using `with`, the file is closed automatically which saves resources.

```{literalinclude} /../../../examples/pylint/r1732_consider_using_with.py

```

Corrected version:

```python
with open('my_file.txt', 'r') as file:
    ... # No need to manually close the file
```

(R1734)=

### Use list literal (R1734)

This error occurs when `list()` is used instead of `[]` to create an empty list.

```{literalinclude} /../../../examples/pylint/r1734_use_list_literal.py

```

The above can be modified to:

```python
lst = [1, 2, 3, 4]
even_lst = []  # This is a fixed version.

for x in lst:
    if x % 2 == 0:
        even_lst.append(x)
```

(R1735)=

### Use dict literal (R1735)

This error occurs when `dict()` is used instead of `{}` to create an empty dictionary.

```{literalinclude} /../../../examples/pylint/r1735_use_dict_literal.py

```

Corrected version:

```python
students_info = [[1002123, "Alex H", "CS"], [1001115, "Jack K", "PSY"]]

cs_student_dict = {}  # This is a fixed version.

for student in students_info:
    if student[2] == "CS":
        cs_student_dict[student[0]] = student[1]
```

(W3301)=

### Nested min-max (W3301)

This error occurs when there are nested calls of `min` or `max` instead of using a single `min`/`max` call.

Note that using a single `min`/`max` call is perfectly fine since you can pass in an arbitrary number of arguments.

```{literalinclude} /../../../examples/pylint/w3301_nested_min_max.py

```

Corrected version:

```python
smallest = min(12, 1, 2)

largest = max(12, 1, 2)
```

## Documentation and naming

Good documentation and identifiers are essential for writing software. PyTA helps check to make sure
we haven't forgotten to document anything, as well as a basic check on the formatting of our
identifiers.

(C0112)=

### Empty Docstring (C0112)

This error occurs when a module, function, class or method has an empty docstring.

```{literalinclude} /../../../examples/pylint/c0112_empty_docstring.py

```

(C9960)=

### Unmentioned Parameter (C9960)

This error occurs when a function parameter is not explicitly mentioned in the docstring. Parameters should be clearly documented
in the function's docstring, not just within doctests or other parts of the function. By default, this checker is disabled.

```{literalinclude} /../../../examples/custom_checkers/c9960_unmentioned_parameter.py

```

(C0103)=

### Invalid name (C0103)

This error occurs when a name does not follow
the [Python Naming Convention][pep8: naming conventions] associated with its role (constant,
variable, etc.).

- Names of variables, attributes, methods, and arguments should be
  in **`lowercase_with_underscores`**.
- Names of constants should be in **`ALL_CAPS_WITH_UNDERSCORES`**.
- Names of classes should be in **`CamelCase`**.

A special character accepted in all types of names is `_`. Numbers are allowed in all names, but
names must not begin with a number.

```{literalinclude} /../../../examples/pylint/c0103_invalid_name.py

```

(C0104)=

### Disallowed name (C0104)

This error occurs when a variable name is chosen to be a typical generic name, rather than a
meaningful one. Here are some of the disallowed names to avoid:

- `foo`
- `bar`
- `baz`
- `toto`
- `tutu`
- `tata`

```{literalinclude} /../../../examples/pylint/c0104_disallowed_name.py

```

(E0102)=

### Function redefined (E0102)

This error occurs when a function, class or method is redefined. If we are getting this error, we
should make sure all the functions, methods and classes that we define have different names.

```{literalinclude} /../../../examples/pylint/e0102_function_redefined.py

```

(E0108)=

### Duplicate argument name (E0108)

This error occurs if there are duplicate parameter names in function definitions. All parameters
must have distinct names, so that we can refer to each one separately in the function body.

```{literalinclude} /../../../examples/pylint/e0108_duplicate_argument_name.py

```

(R1704)=

### Redefined argument from local (R1704)

This error occurs when a local name is redefining the name of a parameter.

```{literalinclude} /../../../examples/pylint/r1704_redefined_argument_from_local.py

```

Corrected version:

```python
def greet_person(name, friends) -> None:
    """Print the name of a person and all their friends."""
    print("My name is {}".format(name))
    for friend in friends:
        print("I am friends with {}".format(friend))
```

**See also**: [](W0621)

(W0621)=

### Redefined outer name (W0621)

This error occurs when we are redefining a variable name that has already been defined in the outer
scope.

For example, this error will occur when we have a local name identical to a global name. The local
name takes precedence, but it hides the global name, making it no longer accessible. Note that the
global name is not accessible _anywhere_ in the function where it is redefined, even before the
redefinition.

```{literalinclude} /../../../examples/pylint/w0621_redefined_outer_name.py

```

(W0622)=

### Redefined builtin (W0622)

This error occurs when we are redefining a built-in function, constant, class, or exception.

```{literalinclude} /../../../examples/pylint/w0622_redefined_builtin.py

```

The following is a list of [builtin functions][built-in functions] in Python 3.6.

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

(C9103)=

### Naming convention violation (C9103)

This error aims to provide a more detailed and beginner-friendly error message about how a variable name violated Python naming conventions.

Again, refer to the [Python Naming Conventions][pep8: naming conventions] for further details but as a quick reminder:

- Avoid using the single character variable names `l`, `O`, or `I` as they are indistinguishable from the numbers zero and one.
- Names of variables, attributes, methods, and arguments should be in **`snake_case`**.
- Names of constants should be in **`UPPER_CASE_WITH_UNDERSCORES`**.
- Names of classes, exceptions, type variables and type aliases should be in **`PascalCase`**.
- Numbers are allowed in names but names cannot start with a number.
- Names should not exceed 30 characters, with the exception of type variables and type aliases which have a limit of 20.

And a quick reminder on the previously mentioned types of naming conventions:

- **`snake_case`**: only lowercase words with each word separated by an underscore "`_`".
- **`UPPER_CASE_WITH_UNDERSCORES`** only uppercase words with each word separated by an underscore "`_`".
- **`PascalCase`**: capitalize the first letter of each word with no separation between each word.

```{literalinclude} /../../../examples/custom_checkers/c9103_naming_convention_violation.py

```

**Note:** this checker is intended to replace C0103 (invalid-name).

(C9104)=

### Module name violation (C9104)

This error occurs when the name of a module violates Python naming conventions. The names of modules should be in **`snake_case`** and should not exceed 30 characters.

## Imports

There are standards governing how we should organize our imports, or even possibly which modules we
may import at all.

(E9999)=

### Forbidden imports (E9999)

This error occurs when your code imports a module which is not allowed (usually for the purpose of
an assignment/exercise).

```{literalinclude} /../../../examples/custom_checkers/e9999_forbidden_import.py
---
lines: 1-3
---
```

PythonTA allows you to specify all the modules that you wish to allow for a particular file
using the `allowed-import-modules` configuration option:

```python
import python_ta
python_ta.check_all(..., config={'allowed-import-modules': ["random"]})
```

You can specify any additional modules you want to allow for import using the
`extra-imports` configuration option:

```python
import python_ta
python_ta.check_all(..., config={'extra-imports': ["math", "tkinter"]})
```

You can also use a configuration file to specify both the `allowed-import-modules` and `extra-imports`.

```ini
[FORBIDDEN IMPORT]
allowed-import-modules = random
extra-imports = math, tkinter
```

In addition, you can specify if you want to allow for local imports through `allow-local-imports` option:

```python
import python_ta
python_ta.check_all(..., config={'allow-local-imports': True})
```

(E0401)=

### Import error (E0401)

The module is unable to be imported. Check the spelling of the module name, or whether the module is
in the correct directory.

```{literalinclude} /../../../examples/pylint/e0401_import_error.py

```

There are other forms of import statements that may cause this error. For example:

```python
import missing_module as foo  # This module does not exist
```

(E0611)=

### No name in module (E0611)

This error occurs when we are trying to access a variable from an imported module, but that variable
name could not be found in that referenced module.

```{literalinclude} /../../../examples/pylint/e0611_no_name_in_module.py

```

(W0401)=

### Wildcard import (W0401)

We should only import what we need. Wildcard imports (shown below) are generally discouraged, as
they add all objects from the imported module into the global namespace. This makes it difficult to
tell in which module a particular class, function or constant is defined, and may cause problems,
for example, when multiple modules have objects with identical names.

```{literalinclude} /../../../examples/pylint/w0401_wildcard_import.py

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

(W0404)=

### Reimported (W0404)

A module should not be imported more than once.

```{literalinclude} /../../../examples/pylint/w0404_reimported.py

```

(W0406)=

### Import self (W0406)

A module should not import itself. For example, if we have a module named `W0406_import_self`, it
should not import a module with the same name.

```{literalinclude} /../../../examples/pylint/w0406_import_self.py

```

This error can occur when the name of our Python file conflicts with the name of a module which we
would like to import. For example, if we have a Python file named `math.py`, calling `import math`
from within that file (or from within _any_ Python file in the same directory) will import _
our_ `math.py` file, and not the [`math` module] from the standard library.

(W0416)=

### Shadowed import (W0416)

This error occurs when a module is imported with an aliased name that has already been used by a
previous import. This prevents the original module from ever being used later in your code.

```{literalinclude} /../../../examples/pylint/w0416_shadowed_import.py

```

(R0401)=

### Cyclic import (R0401)

A module should not import a file which results in an import of the original module.

Example File 1

```{literalinclude} /../../../examples/pylint/r0401_cyclic_import.py

```

Example File 2

```{literalinclude} /../../../examples/pylint/cyclic_import_helper.py

```

(R0402)=

### Consider using from import (R0402)

Some imports are long and go through multiple layers of packages or modules. It's common to want to
rename these imports as the last imported module or package using the `as` keyword.
Consider using the `from` import syntax instead.

```{literalinclude} /../../../examples/pylint/r0402_consider_using_from_import.py

```

Corrected version:

```python
from python_ta import contracts
```

(C0410)=

### Multiple imports (C0410)

Different modules should not be imported on a single line.

```{literalinclude} /../../../examples/pylint/c0410_multiple_imports.py

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

(C0411)=

### Wrong import order (C0411)

This error occurs when the [PEP8 import order][pep8 imports] is not respected. We should do standard
library imports first, then third-party libraries, then local imports.

```{literalinclude} /../../../examples/pylint/c0411_wrong_import_order.py

```

(C0412)=

### Ungrouped imports (C0412)

Imports should be grouped by package.

```{literalinclude} /../../../examples/pylint/c0412_ungrouped_imports.py

```

Corrected version:

```python
from sys import byteorder, stdin  # Same packages should be grouped
from math import floor
```

(C0413)=

### Wrong import position (C0413)

Imports should be placed at the top of the module, above any other code, but below the module
docstring.

```{literalinclude} /../../../examples/pylint/c0413_wrong_import_position.py

```

(C0415)=

### Import outside toplevel (C0415)

Imports should be placed at the top-level of the module, not inside function or class bodies.

```{literalinclude} /../../../examples/pylint/c0415_import_outside_toplevel.py

```

(W0611)=

### Unused import (W0611)

This error occurs when we import a module which is not used anywhere in our code.

```{literalinclude} /../../../examples/pylint/w0611_unused_import.py

```

## Classes and objects

(R0902)=

### Too many instance attributes (R0902)

The class has too many instance attributes, which suggests that it is too complicated and tries to
do too many things.

**Note**: The checker limit is 7 instance attributes.

```{literalinclude} /../../../examples/pylint/r0902_too_many_instance_attributes.py

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

(W0223)=

### Abstract method (W0223)

This error occurs when an abstract method (i.e. a method with a `raise NotImplementedError`
statement) is not overridden inside a subclass of the abstract class.

```{literalinclude} /../../../examples/pylint/w0223_abstract_method.py

```

Corrected version:

```python
class Cat(Animal):
    """A worthy companion."""

    def make_sound(self) -> str:
        return 'Miew...'
```

(W0221)=

### Arguments differ (W0221)

This error occurs when a method takes a different number of arguments than the interface that it
implements or the method that it overrides.

```{literalinclude} /../../../examples/pylint/w0221_arguments_differ.py

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

(W0222)=

### Different method signature (W0222)

When a child class overrides a method of the parent class, the new method should have the same
signature as the method which it is overriding. In other words, the names and the order of the
parameters should be the same in the two methods. Furthermore, if a parameter in the parent method
has a default argument, it must also have a default argument in the child method.

```{literalinclude} /../../../examples/pylint/w0222_signature_differs.py

```

Corrected version:

```python
class PremiumBankAccount(StandardBankAccount):
    ...

    def withdraw(self, amount: float = 200) -> float:  # Note the default argument
        ...
```

(E0101)=

### Return in `__init__` (E0101)

This error occurs when the [`__init__`] method contains a return statement.

The purpose of the `__init__` method is to initialize the attributes of an object. `__init__` is
called by the special method [`__new__`] when a new object is being instantiated, and `__new__` will
raise a `TypeError` if `__init__` returns anything other than `None`.

```{literalinclude} /../../../examples/pylint/e0101_return_in_init.py

```

(W0212)=

### Protected member access (W0212)

Attributes and methods whose name starts with an underscore should be considered "private" and
should not be accessed outside of the class in which they are defined.

```{literalinclude} /../../../examples/pylint/w0212_protected_access.py

```

Private attributes and methods can be modified, added, or removed by the maintainer of the class at
any time, which makes external code which uses those attributes or methods fragile. Furthermore,
modifying a private attribute or calling a private method may lead to undefined behavior from the
class.

(W0233)=

### Bad parent init (W0233)

When using inheritance, we should call the `__init__` method of the parent class and not of some
unrelated class.

```{literalinclude} /../../../examples/pylint/w0233_non_parent_init_called.py

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

(W0245)=

### Super without brackets (W0245)

When making a call to a parent class using `super()`, we must always include the brackets since it is a type of function call. Without the brackets, Python may interpret it as the `super` function itself rather than calling the function to access the superclass.

```{literalinclude} /../../../examples/pylint/w0245_super_without_brackets.py

```

Corrected version:

```python
class Animal:
    """A class that represents an animal"""
    def __init__(self) -> None:
        print('This is an animal')


class Cat(Animal):
    """A class that represents a cat"""
    def __init__(self) -> None:
        super().__init__()
        print('This is a cat')
```

(R1725)=

### Super with arguments (R1725)

This error occurs when calling `super()` with the class and instance as these can be ommited from
Python 3.

```{literalinclude} /../../../examples/pylint/r1725_super_with_arguments.py

```

Corrected Version:

```python
class DummyClass:
    def __init__(self):
        super().__init__()  # Error was on this line
```

(W0201)=

### Attribute defined outside init (W0201)

Any attribute we define for a class should be created inside the `__init__` method. Defining it
outside this method is considered bad practice, as it makes it harder to keep track of what
attributes the class actually has.

```{literalinclude} /../../../examples/pylint/w0201_attribute_defined_outside_init.py

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

(E0202)=

### Method hidden (E0202)

If we accidentally hide a method with an attribute, it can cause other code to attempt to invoke
what it believes to be a method, which will fail since it has become an attribute instead. This will
cause the program to raise an error.

```{literalinclude} /../../../examples/pylint/e0202_method_hidden.py

```

(E0203)=

### Access to member before definition (E0203)

Before trying to use a member of a class, it should have been defined at some point. If we try to
use it before assigning to it, an error will occur.

```{literalinclude} /../../../examples/pylint/e0203_access_member_before_definition.py

```

(E0302)=

### Unexpected special method signature (E0302)

This error occurs when a special method (also known as
a ["dunder method"][python double-under, double-wonder], because it has double underscores or "
dunders" on both sides) does not have the expected number of parameters. Special methods have an
expected signature, and if we create a method with the same name and a different number of
parameters, it can break existing code and lead to errors.

```{literalinclude} /../../../examples/pylint/e0302_unexpected_special_method_signature.py

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

(E0239)=

### Inheriting from a non-class (E0239)

A new class can only inherit from a different class (i.e. a Python object which defines the _type_
of an object). It cannot inherit from an instance of a class or from a Python literal such as a
string, list, or dictionary literal.

```{literalinclude} /../../../examples/pylint/e0239_inherit_non_class.py

```

Corrected version:

```python
class FancyFloat(float):
    """A fancy floating point number."""
    pass
```

(E0241)=

### Duplicate bases (E0241)

A class should not inherit from a different class multiple times.

```{literalinclude} /../../../examples/pylint/e0241_duplicate_bases.py

```

(E0211)=

### No method argument (E0211)

Each method in a class needs to have at least one parameter, which by convention we name `self`.
When we create an instance of a class and call an instance method, Python automatically passes the
class instance as the first argument to the method. If a method does not expect any arguments, this
will result in an error.

```{literalinclude} /../../../examples/pylint/e0211_no_method_argument.py

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

(E0213)=

### `self` as the first argument (E0213)

The first parameter of a method should always be called `self`. While it is possible to name the
first parameter something else, using the word `self` is a convention that is strongly adhered to by
the Python community and makes it clear that we did not simply forget to add `self` or accidentally
intended a function as a method.

```{literalinclude} /../../../examples/pylint/e0213_no_self_argument.py

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

(R0201)=

### No self use (R0201)

If a method does not make use of the first argument `self`, it means that the task that the method
is performing is not linked to the class of which it is a member. In such a case, we should rewrite
the method as a function (by removing the first parameter `self`) and move it outside the class.

In the following example, `add_small_coins` does not make use of the first parameter `self` and so
can be moved outside the class as a function.

```{literalinclude} /../../../examples/pylint/r0201_no_self_use.py

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

(W0211)=

### Bad static method argument (W0211)

This error occurs when a static method has `self` as the first parameter. Static methods are methods
that do not operate on instances. If we feel that the logic of a particular function belongs inside
a class, we can move that function into the class and add
a [`@staticmethod`][python documentation: staticmethod] [decorator][python documentation: decorator]
to signal that the method is a static method which does not take a class instance as the first
argument. If such a static method contains `self` as the first parameter, it suggests that we are
erroneously expecting a class instance as the first argument to the method.

```{literalinclude} /../../../examples/pylint/w0211_bad_staticmethod_argument.py

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

(E3701)=

### Invalid field call (E3701)

The [`dataclasses.field`][dataclass fields] function is used to specify the behaviour of instance attributes when defining a dataclass.
This function returns a `Field` object that contains the arguments that were set in the function. This function should
only be used as the value of an assignment in a dataclass definition or in the `make_dataclass()` function. Any other
use will be considered invalid.

```{literalinclude} /../../../examples/pylint/e3701_invalid_field_call.py

```

Corrected version:

```python
from dataclasses import dataclass, field

@dataclass
class Wallet:
    """A custom class for storing information about a wallet."""
    money: int = field(default=5)
```

## Exceptions

(W0133)=

### Pointless exception statement (W0133)

This error occurs when an exception is created but never assigned, raised or returned for use anywhere in the code.

```{literalinclude} /../../../examples/pylint/w0133_pointless_exception_statement.py

```

This error can be resolved by assigning, raising or returning the exception as demonstrated below:

```python
def reciprocal(num: float) -> float:
    """Return 1 / num."""
    if num == 0:
        raise ValueError('num cannot be 0!')
    else:
        return 1 / num
```

(W0134)=

### Return in finally (W0134)

This error occurs when a `return` statement is used inside a `finally` block. Doing so overwrites any previous return
values therefore should be avoided.

For example, in the code example below, if an `IndexError` occurs we want
`error_codes[1]` to be returned, however since there is a return statement in the `finally` block `error_codes[2]` will be
returned instead. Moving that return statement outside the `finally` block would resolve the issue.

```{literalinclude} /../../../examples/pylint/w0134_return_in_finally.py

```

Corrected Version:

```python
def error_code(error_codes):

    try:
        print(error_codes[0])
    except IndexError:
        return error_codes[1]

    return error_codes[2]
```

(W0702)=

### Bare exception (W0702)

If the `except` keyword is used without being passed an exception, _all exceptions will be caught_.
This is not good practice, since we may catch exceptions that we do not want to catch. For example,
we typically do not want to catch the [`KeyboardInterrupt`][python documentation: keyboardinterrupt]
exception, which is thrown when a user attempts to exist the program by typing `Ctrl-C`.

```{literalinclude} /../../../examples/pylint/w0702_bare_except.py

```

(W0718)=

### Broad exception caught (W0718)

Using `except Exception:` is only slightly more specific than `except:` and should also be avoided (
see [W0702](#W0702)). Since most builtin exceptions, and all user-defined exceptions, are derived
from the `Exception` class, using `except Exception:` provides no information regarding which
exception actually occurred. Exceptions which we do not expect can go unnoticed, and this may lead
to bugs.

```{literalinclude} /../../../examples/pylint/w0718_broad_exception_caught.py

```

(W0719)=

### Broad exception raised (W0719)

This error is emitted when one raises a generic exception. Raising exceptions that are not specific will cause the
program to catch generic exceptions. This is bad practice because we may catch exceptions that we don't want.
Catching generic exceptions can also hide bugs and make it harder to debug programs.

```{literalinclude} /../../../examples/pylint/w0719_broad_exception_raised.py

```

This error can be resolved by raising a more specific exception:

**Note**: `NameError` is a subclass of `Exception` (it is a more specific type of exception in Python).

```python
raise NameError("The variable x doesn't exist!")
```

(W0705)=

### Duplicate except blocks (W0705)

This error occurs when we try to catch the same exception multiple times. Only the first `except`
block for a particular exception will be reached.

```{literalinclude} /../../../examples/pylint/w0705_duplicate_except.py

```

(E0701)=

### Bad exception order (E0701)

Except blocks are analyzed sequentially (from top to bottom) and the first block that meets the
criteria for catching the exception will be used. This means that if we have a generic exception
type before a specific exception type, the code for the specific exception type will never be
reached.

```{literalinclude} /../../../examples/pylint/e0701_bad_except_order.py

```

(W0711)=

### Binary op exception (W0711)

The Python `except` statement can catch multiple exceptions, if those exceptions are passed as a
tuple. It is possible (but incorrect!) to pass `except` an expression containing the exception
classes separated by a binary operator such as `and` or `or`. In such a case, only one of the
exceptions will be caught!

```{literalinclude} /../../../examples/pylint/w0711_binary_op_exception.py

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

(E0704)=

### Misplaced bare raise (E0704)

The Python `raise` statement can be used without an expression only inside an `except` block. In
this case, it will re-raise the exception that was caught by the `except` block. This may be useful
if, for example, we wish to do some cleanup (e.g. close file handles), or print an error message,
before passing the exception up the call stack.

```{literalinclude} /../../../examples/pylint/e0704_misplaced_bare_raise.py

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

(E0702)=

### Raising bad type (E0702)

The Python `raise` statement expects an object that is derived from
the [`BaseException`][python documentation: baseexception] class. We cannot call `raise` on integers
or strings.

```{literalinclude} /../../../examples/pylint/e0702_raising_bad_type.py

```

**See also**: [E0710](#E0710)

(E0710)=

### Raising non-exception (E0710)

The Python `raise` statement expects an object that is derived from
the [`BaseException`][python documentation: baseexception] class. All user-defined exceptions should
inherit from the [`Exception`][python documentation: exception] class (which will make them indirect
descendents of the `BaseException` class). Attempting to raise any other object will lead to an
error.

```{literalinclude} /../../../examples/pylint/e0710_raising_non_exception.py

```

(E0711)=

### NotImplemented raised (E0711)

[`NotImplemented`][python documentation: notimplemented] should only be used as a return value for
binary special methods, such as `__eq__`, `__lt__`, `__add__`, etc., to indicate that the operation
is not implemented with respect to the other type. It is _not interchangeable_
with [`NotImplementedError`][python documentation: notimplementederror], which should be used to
indicate that the abstract method must be implemented by the derived class.

```{literalinclude} /../../../examples/pylint/e0711_notimplemented_raised.py

```

(E0712)=

### Catching non-exception (E0712)

The Python `raise` statement expects an object that is derived from
the [`BaseException`][python documentation: baseexception] class (see [E0710](#E0710)). Accordingly,
the Python `except` statement also expects objects that are derived from
the [`BaseException`][python documentation: baseexception] class. Attempting to call `except` on any
other object will lead to an error.

```{literalinclude} /../../../examples/pylint/e0712_catching_non_exception.py

```

## Custom errors

(E9997)=

### Global variables (E9997)

When writing Python programs, your variables should always be defined within functions.
(A _global variable_ is a variable that isn't defined within a function.)

Example:

```{literalinclude} /../../../examples/custom_checkers/e9997_forbidden_global_variables.py
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

(E9992)=

### Top Level Code (E9992)

This error occurs when code statements are placed in the top level.
The type of statements allowed in the top level are imports, function/class definitions,
assignment to constants, and the main block.

Example:

```{literalinclude} /../../../examples/custom_checkers/e9992_forbidden_top_level_code.py

```

To fix this, you could place the testing code inside the main block. For example:

```python
def example_function(name: str) -> str:
    return f'Hello {name}!'


if __name__ == '__main__':
    print(example_function('Fred'))

```

(E9998)=

### Forbidden IO function (E9998)

Input / output functions ([`input`], [`open`] and [`print`]) should not be used unless explicitly
required. If `print` calls are used to debug the code, they should be removed prior to submission.

Example:

```{literalinclude} /../../../examples/custom_checkers/e9998_forbidden_IO_function.py

```

By default, there are no input/output functions ([`input`], [`open`] and [`print`]) allowed.
However, users may want to specify the permissible functions for utilizing input/output operations.
Use the `allowed-io` option to specify **a list of function names** where input/output functions are allowed.
For example, suppose the user defined a Python function as follows:

```python
def hello_world() -> None:
    """The first steps in learning Python"""

    print('Hello World')    # Error on this line (print is an I/O function)
```

Use the following configuration to allow the usage of an input/output function ([`print`] in this case):

```python
import python_ta
python_ta.check_all(config={
    'allowed-io': ['hello_world']
})
```

The exception is calling IO functions inside the main block, which is allowed.

```python
if __name__ == "__main__":
    name = input()
```

By default, [`input`], [`open`] and [`print`] are not allowed. However, you can choose which I/O functions/methods
specifically to disallow using the `forbidden-io-functions` option. This takes a list of function names and method
[qualified names](https://peps.python.org/pep-3155/#proposal) that should not be used. For example, use the
following configuration to forbid the use of [`print`] and `MyClass.method` but allow [`input`] and [`open`]:

```python
import python_ta
python_ta.check_all(config={
    "forbidden-io-functions": ["print", "MyClass.method"]
})
```

(E9996)=

### Loop iterates only once (E9996)

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

(E9993)=

### Invalid Range Index (E9993)

This error occurs when we call the `range` function but with argument(s) that would cause the range
to be empty or only have one element.

Examples:

```{literalinclude} /../../../examples/custom_checkers/e9993_invalid_range_index.py

```

When such `range`s are used with a loop, the loop will iterate either zero or one time, which is
almost certainly not what we intended! This usually indicates an error with how `range` is called.

(E9994)=

### Unnecessary Indexing (E9994)

This error occurs when we use a for loop or comprehension that goes over a range of indexes for a list, but only use
those indexes to access elements from the list.

Example (For loop):

```{literalinclude} /../../../examples/custom_checkers/e9994_unnecessary_indexing.py
---
lines: 5-11
---
```

We can simplify the above code by changing the loop to go over the elements of the list directly:

```python
def sum_items(lst: list[int]) -> int:
    """Return the sum of a list of numbers."""
    s = 0
    for x in lst:
        s += x

    return s
```

Example (Comprehension):

```{literalinclude} /../../../examples/custom_checkers/e9994_unnecessary_indexing.py
---
lines: 98-100
---
```

We can simplify the above code by changing the comprehension to go over the elements of the list directly:

```python
def list_comp(lst: list) -> list:
    """Return all the items in lst in a new list."""
    return [x for x in lst]
```

In general, we should only loop over indexes (`for i in range(len(lst))`) if we are using the index
for some purpose other than indexing into the list.
One common example is if we want to iterate over two lists in parallel:

For loop:

```python
def print_sum(lst1: list[int], lst2: list[int]) -> None:
    """Print the sums of each corresponding pair of items in lst1 and lst2.
    Precondition: lst1 and lst2 have the same length.
    """
    for i in range(len(lst1)):
        print(lst1[i] + lst2[i])
```

Comprehension:

```python
def parallel_lst(lst1: list[int], lst2: list[int]) -> list:
    """Return a list of the concatenation of the values of lst1 and lst2 at index i.
    Precondition: lst1 and lst2 have the same length."""
    return [lst1[i] + lst2[i] for i in range(len(lst1))]
```

(E9984)=

### For Target Subscript (E9984)

This error occurs when an index variable in a for loop or comprehension uses indexing notation, which can occur if you mix up the
index variable and the list being iterated over.

Example (For loop):

```{literalinclude} /../../../examples/custom_checkers/e9984_invalid_for_target.py
---
lines: 5-10
---
```

Example (Comprehension):

```{literalinclude} /../../../examples/custom_checkers/e9984_invalid_for_target.py
---
lines: 54-56
---
```

To fix this, always use a brand-new variable name for your index variable.
For example:

For loop:

```python
def example1(lst: list[int]) -> int:
    s = 0
    for number in lst:  # Fixed
        s += number
    return s
```

Comprehension:

```python
def example7(lst: list[int]) -> list[int]:
    return [number for number in lst]  # Fixed
```

(E9969)=

### Possibly undefined variable (E9969)

This error occurs when we use a variable that might not be defined prior to its use.
The most common cause is when we define a variable in one branch of an if statement, but not another.

Example:

```{literalinclude} /../../../examples/custom_checkers/e9969_possibly_undefined.py

```

(E9959)=

### Redundant assignment (E9959)

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

(E9988)=

### Shadowing in comprehension (E9988)

This error occurs when a variable in a comprehension shadows (i.e., has the same name as) a variable
from an outer scope, such as a local variable in the same function.
In general you should avoid reusing variable names within the same function, and so you can fix this
error by renaming the variable in the comprehension.

Example:

```{literalinclude} /../../../examples/custom_checkers/e9988_shadowing_in_comprehension.py
---
lines: 10-12
---
```

(E9970)=

### Missing parameter type (E9970)

This error occurs when we have written a function definition but are missing a type annotation for
a parameter.

Example:

```{literalinclude} /../../../examples/custom_checkers/e9970_missing_param_type.py
---
lines: 2-4
---
```

(E9995)=

### Type is assigned (E9995)

This error occurs when a type is not annotated but rather assigned in a function or class definition.
In Python, default values for function arguments and class instance variables are assigned using `=` during their respective definitions.
Type annotations, on the other hand, are declared using `:`.
Below is a correct usage of assigning default values and annotating types.

```python
def print_str_argument(str_argument: str = "Some default value."):
    print(str_argument)


class BirthdayCake:
    number_of_candles: int = 1 # 1 is the default value
```

An incorrect usage of assigning default values and annotating types is shown below.
Example:

```{literalinclude} /../../../examples/custom_checkers/e9995_type_is_assigned.py

```

To fix these errors, one may make the following changes.

```python
from __future__ import annotations
import datetime


class Person:
    name = "Bob"


def add_two_numbers(
    x: int,
    y: list[float],
    z: type = complex
) -> int:
    return (x + y) * z


class MyDataType:
    x: datetime.time
    y: Person
    z: complex = complex
```

(E9971)=

### Missing return type (E9971)

This error occurs when we have written a function definition but are missing a type annotation for
the return value. Use `None` as the type annotation if the function does not return anything.

Example:

```{literalinclude} /../../../examples/custom_checkers/e9971_missing_return_type.py
---
lines: 2-4
---
```

(E9920)=

### Unnecessary f-string (E9920)

This error occurs when we use an f-string to represent a single, unjoined expression without specifying
any formatting.

Example:

```{literalinclude} /../../../examples/custom_checkers/e9920_unnecessary_f_string.py
---
lines: 8-14
---
```

These f-strings can be directly replaced with the expression or after casting the expression to a string first.
For example:

```python
x = "hello"

a = x  # or a = str(x)

c = x + ' world'  # or c = str(x + ' world')
```

(E9930)=

### Simplifiable if (E9930)

This error occurs when an `if` or `elif` branch (with no other branches below it) only contains a single nested `if` statement with a single branch.

Example:

```python
x = 5
if x > 5:
    x += 1
elif x < -5:
    if x % 2 == 0:
        x -= 1
```

The nested `if` statement can be removed and its test condition can be added to the `elif` branch immediately above it.

For example:

```python
x = 5
if x > 5:
    x += 1
elif x < -5 and x % 2 == 0:
    x -= 1
```

(E9972)=

### Missing attribute type (E9972)

This error occurs when we have written a class but are missing a type annotation for an
instance attribute assigned in the class initializer.

Example:

```{literalinclude} /../../../examples/custom_checkers/e9972_missing_attribute_type.py
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

(E9973)=

### Missing space in doctest (E9973)

This error occurs when a doctest found in the docstring of a function is not followed by a space.
In this case the doctest will not actually be parsed.

Example:

```{literalinclude} /../../../examples/custom_checkers/e9973_missing_space_in_doctest.py
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

(E9980)=

### Invalid syntax in function precondition (E9980)

This error occurs when a function precondition contains invalid Python expression syntax. Valid Python statements
(e.g. assignment statements like x = 5) are also flagged, as they aren't valid Python expressions.
Multi-line preconditions are supported using a backslash ('\') following a space at the end of each line except the last.

Example:

```{literalinclude} /../../../examples/custom_checkers/e9980_invalid_precondition_syntax.py
---
lines: 8-10
---
```

The first precondition incorrectly attempts to use the inequality operator (!=), which is not valid Python syntax.
This should be corrected to use Python's inequality operator:

```python
def demo_function(x: int, y: int) -> int:
    """Demonstrates e9980_invalid_precondition_syntax

    Preconditions:
       - x != 0
       - y != 0
    """
    return x // y
```

(E9981)=

### Invalid syntax in function postcondition (E9981)

This error occurs when a function postcondition contains invalid Python expression syntax. Valid Python statements
(e.g. assignment statements like x = 5) are also flagged, as they aren't valid Python expressions.
Multi-line postconditions are supported using a backslash ('\') following a space at the end of each line except the last.
The identifier `$return_value` can be used to refer to the return value of the function within postcondition statements.

Example:

```{literalinclude} /../../../examples/custom_checkers/e9981_invalid_postcondition_syntax.py
---
lines: 8-10
---
```

The first precondition incorrectly has a whitespace in the middle of the greater than or equal to operator, which is not valid Python syntax.
This should be corrected to use Python's the middle of the greater than or equal to operator:

```python
def demo_function(x: int, y: int) -> int:
    """Demonstrates e9981_invalid_postcondition_syntax

    Postconditions:
       - $return_value >= 0
       - $return_value != y
    """
    return max(0, x // y)
```

(E9989)=

### Pycodestyle errors (E9989)

These errors are based on the Python code style guidelines ("PEP8") published by the Python team.
These errors do not affect the functionality of your code, but can affect its readability.
The error messages display how to fix them (e.g., by adding spaces or adding/removing blank lines).

See also: [PEP 8 -- Style Guide for Python Code](https://www.python.org/dev/peps/pep-0008/)

By default, all styling guidelines checked by `pycodestyle` are reported. To ignore a specific check, use the
`pycodestyle-ignore` option. This takes in a list of error codes from [pycodestyle error codes](https://pycodestyle.pycqa.org/en/latest/intro.html#error-codes)
to ignore. For example, use the following configuration to ignore E302 (expected 2 blank lines, found 0), and
E305 (expected 2 blank lines after end of function or class):

```python
import python_ta
python_ta.check_all(config={"pycodestyle-ignore": ["E302", "E305"]})
```

(R0133)=

### Comparison of constants (R0133)

This error occurs when two constants are compared with each other. The result of the comparison is always the same.
It is better to use the constant directly.

```{literalinclude} /../../../examples/pylint/r0133_comparison_of_constants.py

```

Corrected version:

```python
def is_equal_to_one(a: int) -> bool:
    return a == 1
```

(E9950)=

### Forbidden Python syntax (E9950)

This error occurs when disallowed Python syntax is used in code. Disallowed syntax refers to any
Python syntax that shouldn't be used because it defeats the purpose of an assessment. Used for
teaching purposes.

Example:

```{literalinclude} /../../../examples/custom_checkers/e9950_forbidden_python_syntax.py

```

By default, all Python syntax is allowed. To forbid a specific type of syntax, use the disallowed-python-syntax
option. This takes a list of names of [AST nodes from astroid](https://pylint.pycqa.org/projects/astroid/en/latest/api/astroid.nodes.html)
to forbid. For example, use the following configuration to forbid break and continue statements, comprehensions,
and for and while loops:

```python
import python_ta
python_ta.check_all(config={
    "disallowed-python-syntax": ["Break", "Continue", "Comprehension", "For", "While"]
})
```

(R9900)=

### Redundant Condition (R9900)

This error occurs when an `if` or `while` condition is guaranteed to be true.

Example:

```{literalinclude} /../../../examples/custom_checkers/r9900_redundant_condition.py

```

This error will only be checked if the `z3-solver` library is installed and `z3` option of PythonTA
is enabled:

```python
import python_ta
python_ta.check_all(config={
    "z3": True
})
```

### Impossible Condition (R9901)

This error occurs when an `if` or `while` condition is guaranteed to be false.

Example:

```{literalinclude} /../../../examples/custom_checkers/r9901_impossible_condition.py

```

This error will only be checked if the `z3-solver` library is installed and `z3` option of PythonTA
is enabled:

```python
import python_ta
python_ta.check_all(config={
    "z3": True
})
```

(W9501)=

### Infinite While Loop (W9501)

This error is raised when a `while` loop never terminates, indicating an infinite loop.

Example:

```{literalinclude} /../../../examples/custom_checkers/w9501_infinite_loop.py

```

**Note**: Currently, this error occurs when...

1. None of the variables used in the condition of a `while` loop are updated within the loop body
2. The loop condition is constant (i.e., always True), and there are no exit statements (`return`, `break`, `raise`, `yield`, `sys.exit()`)

This often indicates a logical error that may lead to an infinite loop or a loop that doesn't behave as intended.

## Miscellaneous

(E1305)=

### Too many format args (E1305)

This error occurs when we use the `format` method on a string, but call it with more arguments than
the number of `{}` in the string.

```{literalinclude} /../../../examples/pylint/e1305_too_many_format_args.py

```

Corrected version:

```python
name = "Amy"
age = "17"
country = "England"

s = "{} who is {} lives in {}".format(name, age, country)
```

**See also**: [E1121](#E1121)

(E1306)=

### Too few format args (E1306)

This error occurs when we use the `format` method on a string, but call it with fewer arguments than
the number of `{}` in the string.

```{literalinclude} /../../../examples/pylint/e1306_too_few_format_args.py

```

Corrected version:

```python
s = "{} and {}".format("first", "second")
```

**See also**: [E1120](#E1120)

(W1309)=

### F-string without interpolation (W1309)

This error occurs when there are no interpolation variables present in an f-string. This might indicate that there is
either a bug in the code (that is, there should be an interpolation variable in the f-string) or the f-string can be a
normal string.

```{literalinclude} /../../../examples/pylint/w1309_f_string_without_interpolation.py

```

The issue above can be resolved in 2 ways - either the f-string can be converted into a normal string, or the missing
interpolation variable can be added to the f-string. The snippet below shows both these solutions.

```python
# Using a normal string instead of an f-string
print('Hello World!')

# Adding an interpolation to the f-string
entity = "World"
print(f'Hello {entity}!')
```

**See also**: [W1310](#W1310)

(W1310)=

### Format string without interpolation (W1310)

This error occurs when a format string does not have **any** interpolation variables. This can be an issue as it can
mean that either the string can be a normal string which does not need any formatting, or there is a bug in the code
and there should be interpolation variables in the string.

```{literalinclude} /../../../examples/pylint/w1310_format_string_without_interpolation.py

```

The error above can be resolved as follows:

```python
greeting = 'Hello There, {name}'.format(name='person')
```

**See also**: [W1309](#W1309)

(W1303)=

### Missing format argument key (W1303)

This error occurs when a format string that uses named fields does not receive the required
keywords. In the following example, we should assign three values for `last_name`, `first_name`,
and `age`.

```{literalinclude} /../../../examples/pylint/w1303_missing_format_argument_key.py

```

Corrected version:

```python
s = '{last_name}, {fist_name} - {age}'.format(last_name='bond', first_name='james', age=37)
```

**See also**: [E1120](#E1120), [E1306](#E1120)

(E1310)=

### Bad str strip call (E1310)

This error occurs when we call [`strip`][str.strip], [`lstrip`][str.lstrip],
or [`rstrip`][str.rstrip], but pass an argument string which contains duplicate characters. The
argument string should contain the _distinct_ characters that we want to remove from the end(s) of a
string.

```{literalinclude} /../../../examples/pylint/e1310_bad_str_strip_call.py

```

It is a common mistake to think that `mystring.strip(chars)` removes the substring `chars` from the
beginning and end of `mystring`. It actually removes all characters in `chars` from the beginning
and end of `mystring`, _irrespective of their order_! If we pass an argument string with duplicate
characters to `mystring.strip`, we are likely misinterpreting what this method is doing.

(W1305)=

### Format combined specification (W1305)

This error occurs when a format string contains both automatic field numbering (e.g. `{}`) and
manual field specification (e.g. `{0}`).

For example, we should not use `{}` and `{index}` at the same time.

```{literalinclude} /../../../examples/pylint/w1305_format_combined_specification.py

```

Corrected version:

```python
s = "{} and {}".format("a", "b")
```

or:

```python
s = "{0} and {1}".format("a", "b")
```

(W1401)=

### Anomalous backslash in string (W1401)

This error occurs when a string literal contains a backslash that is not part of an escape sequence.

```{literalinclude} /../../../examples/pylint/w1401_anomalous_backslash_in_string.py

```

The following is a [list of recognized escape sequences][string and bytes literals] in Python string
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

(W1503)=

### Redundant unittest assert (W1503)

The first argument of `assertTrue` and `assertFalse` is a "condition", which should evaluate
to `True` or `False`. These methods evaluate the condition to check whether the test passes or
fails. The conditions should depend on the code that we are testing, and should not be a constant
literal like `True` or `4`. Otherwise, the test will always have the same result, regardless of
whether our code is correct.

```{literalinclude} /../../../examples/pylint/w1503_redundant_unittest_assert.py

```

(C0123)=

### Unidiomatic type check (C0123)

This error occurs when `type` is used instead of `isinstance` to perform a type check.
Use `isinstance(x, Y)` instead of `type(x) == Y`.

```{literalinclude} /../../../examples/pylint/c0123_unidiomatic_typecheck.py

```

The above can be modified to:

```python
def is_int(obj: Union[int, float, str]) -> bool:
    """Check if the given object is of type 'int'."""
    return isinstance(obj, int)
```

**See also**: [C0121](#C0121)

(W0102)=

### Dangerous default value (W0102)

This warning occurs when a mutable object, such as a list or dictionary, is provided as a default
argument in a function definition. Default arguments are instantiated only once, at the time when
the function is defined (i.e. when the interpreter encounters the `def ...` block). If the default
argument is mutated when the function is called, it will remain modified for all subsequent function
calls. This leads to a common "gotcha" in Python, where an "empty" list or dictionary, specified as
the default argument, starts containing values on calls other than the first call.

```{literalinclude} /../../../examples/pylint/w0102_dangerous_default_value.py

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
from __future__ import annotations
from typing import Optional

def make_list(n: int, lst: Optional[list[int]]=None) -> list[int]:
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

(C0201)=

### Consider iterating dictionary (C0201)

It is more _pythonic_ to iterate through a dictionary directly, without calling the `.keys` method.

```{literalinclude} /../../../examples/pylint/c0201_consider_iterating_dictionary.py

```

Corrected version:

```python
for item in menu:
    print("My store sells {}.".format(item))
```

(C0325)=

### Superfluous parens (C0325)

This error occurs when a keyword, such as `if` or `for`, is followed by a single item enclosed in
parentheses. In such a case, parentheses are not necessary.

```{literalinclude} /../../../examples/pylint/c0325_superfluous_parens.py

```

Corrected version:

```python
if 'anchovies' in pizza_toppings:
    print("Awesome!")
```

(R1707)=

### Trailing comma tuple (R1707)

This error occurs when a Python expression is terminated by a comma. In Python, a tuple is created
by the comma symbol, not by parentheses. This makes it easy to create a tuple accidentally, by
misplacing a comma, which can lead to obscure bugs. In order to make our intention clear, we should
always use parentheses when creating a tuple, and we should never leave a trailing comma in our
code.

```{literalinclude} /../../../examples/pylint/r1707_trailing_comma_tuple.py

```

Corrected version:

```python
my_lucky_number = 7
print(my_lucky_number)  # Prints 7
```

(W0199)=

### Assert on tuple (W0199)

This error occurs when an `assert` statement is called with a tuple as the first argument. `assert`
acting on a tuple passes if and only if the tuple is non-empty. This is likely _not_ what the
programmer had intended.

```{literalinclude} /../../../examples/pylint/w0199_assert_on_tuple.py

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

(R0123)=

### Literal comparison (R0123)

This error occurs when we use the identity operator `is` to compare non-boolean Python literals.
Whether or not two literals representing the same value (e.g. two identical strings) have the same
identity can vary, depending on the way the code is being executed, the code that has ran
previously, and the version and implementation of the Python interpreter. For example, each of the
following assertions pass if the lines are evaluated together from a Python file,
but `assert num is 257` and `assert chars is 'this string fails'` fail if the lines are entered into
a Python interpreter one-by-one.

```{literalinclude} /../../../examples/pylint/r0123_literal_comparison.py

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

(W0106)=

### Expression not assigned (W0106)

This error occurs when an expression that is not a function call is not assigned to a variable.
Typically, this indicates that we were intending to do something else.

```{literalinclude} /../../../examples/pylint/w0106_expression_not_assigned.py

```

Corrected version:

```python
lst = [1, 2, 3]
lst.append(4)
print("Appended 4 to my list!")
```

(E0303)=

### Invalid length returned (E0303)

This error occurs when the `__len__` special method returns something other than a non-negative
integer.

```{literalinclude} /../../../examples/pylint/e0303_invalid_length_returned.py

```

Corrected version:

```python
class Company:
    """A company with some employees."""

    def __init__(self, employees: list[str]) -> None:
        self._employees = employees

    def __len__(self) -> int:
        return len(self._employees)
```

(W1515)=

### Forgotten debug statement (W1515)

This warning occurs when debugging breakpoints (such as `breakpoint()`, `sys.breakpointhook()`,
and `pdb.set_trace()`) are found. These breakpoints should be removed in production code.

```{literalinclude} /../../../examples/pylint/w1515_forgotten_debug_statement.py

```

(mypy-based-checks)=

## Mypy-based checks

The following errors are identified by the StaticTypeChecker, which uses Mypy to detect issues related to type annotations in Python code.
Further information on Mypy can be found in its [official documentation](https://mypy.readthedocs.io/en/stable/).

(E9951)=

### Incompatible Argument Type (E9951)

This error occurs when a function is called with an argument that does not match the expected type for that parameter. See the [Mypy documentation](https://mypy.readthedocs.io/en/stable/error_code_list.html#check-argument-types-arg-type).

```{literalinclude} /../../../examples/custom_checkers/static_type_checker_examples/e9951_incompatible_argument_type.py

```

(E9952)=

### Incompatible Assignment (E9952)

This error occurs when an expression is assigned to a variable, but the types are incompatible. See the [Mypy documentation](https://mypy.readthedocs.io/en/stable/error_code_list.html#check-types-in-assignment-statement-assignment).

```{literalinclude} /../../../examples/custom_checkers/static_type_checker_examples/e9952_incompatible_assignment.py

```

(E9953)=

### List Item Type Mismatch (E9953)

This error occurs when a list item has a type that does not match the expected type for that position in the list. See the [Mypy documentation](https://mypy.readthedocs.io/en/stable/error_code_list.html#check-list-items-list-item).

```{literalinclude} /../../../examples/custom_checkers/static_type_checker_examples/e9953_list_item_type_mismatch.py

```

(E9954)=

### Unsupported Operand Types (E9954)

This error occurs when an operation is attempted between incompatible types, such as adding a string to an integer. See the [Mypy documentation](https://mypy.readthedocs.io/en/stable/error_code_list.html#check-uses-of-various-operators-operator).

```{literalinclude} /../../../examples/custom_checkers/static_type_checker_examples/e9954_unsupported_operand_types.py

```

(E9955)=

### Union Attribute Error (E9955)

This error occurs when attempting to access an attribute on a `Union` type that may not exist on all possible types in the union. See the [Mypy documentation](https://mypy.readthedocs.io/en/stable/error_code_list.html#check-that-attribute-exists-in-each-union-item-union-attr).

```{literalinclude} /../../../examples/custom_checkers/static_type_checker_examples/e9955_union_attr_error.py

```

(E9956)=

### Dictionary Item Type Mismatch (E9956)

This error occurs when a dictionary entry contains a key or value type that does not match the expected type. See the [Mypy documentation](https://mypy.readthedocs.io/en/stable/error_code_list.html#check-dict-items-dict-item).

```{literalinclude} /../../../examples/custom_checkers/static_type_checker_examples/e9956_dict_item_type_mismatch.py

```

## Modified iterators in for loops

(W4701)=

### Modified iterating list (W4701)

This error occurs when a list is modified inside a for loop by adding or removing items from the `list`. Other types of modification are okay, and do not trigger the error. A copy of the `list` can be used instead.

```{literalinclude} /../../../examples/pylint/w4701_modified_iterating_list.py

```

(E4702)=

### Modified iterating dict (E4702)

This error occurs when a dictionary is modified inside a for loop by adding or removing items from the `dict`. Other types of modification (like assigning a new value to an existing key) are actually okay, and do not trigger the error. A copy of the `dict` can be used instead.

```{literalinclude} /../../../examples/pylint/e4702_modified_iterating_dict.py

```

(E4703)=

### Modified iterating set (E4703)

This error occurs when a set is modified inside a for loop by adding or removing items from the `set`. Other types of modification are actually okay, and do not trigger the error. A copy of the `set` can be used instead.

```{literalinclude} /../../../examples/pylint/e4703_modified_iterating_set.py

```

(#style) =

## Style errors

(C0321)=

### Multiple statements (C0321)

This error occurs when we write more than one statement on a single line. According to PEP8, [_
multiple statements on the same line are discouraged_][pep8: other recommendations].

```{literalinclude} /../../../examples/pylint/c0321_multiple_statements.py

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

(W0301)=

### Unnecessary semicolon (W0301)

This error occurs when we end a Python statement with a semicolon. There is no good reason to ever
use a semicolon in Python.

```{literalinclude} /../../../examples/pylint/w0301_unnecessary_semicolon.py

```

Corrected version:

```python
print("Hello World!")
```

(C0304)=

### Missing final newline (C0304)

This error occurs when a file is missing a trailing newline character. For example, if we represent
a (typically invisible) newline character as `¬`, the following file would raise this error:

```{literalinclude} /../../../examples/pylint/c0304_missing_final_newline.py

```

while the corrected file which contains a trailing newline character would not:

```python
print("Hello World!")  # Trailing newline is present:  ¬
```

(C0305)=

### Trailing newlines (C0305)

This error occurs when a file ends with more than one newline character (i.e. when a file contains
trailing blank lines). For example:

```{literalinclude} /../../../examples/pylint/c0305_trailing_newlines.py

```

Corrected version:

```python
print("Hello World!")  # This file ends with a single newline character! :)
```

(C2503)=

### Bad file encoding (C2503)

This error occurs when there is an encoding declaration at the top of the Python file.

```{literalinclude} /../../../examples/pylint/c2503_bad_file_encoding.py

```

(C0301)=

### Line too long (C0301)

This error occurs when a line is longer than a predefined number of characters. Our default limit
for all lines is 80 characters.

```{literalinclude} /../../../examples/pylint/c0301_line_too_long.py

```

(W3601)=

### Bad chained comparison (W3601)

This error occurs when a chained comparison uses incompatible comparison operators, i.e. operators that perform a different kind of test. For example,
`<` has a different meaning than `is` and `in`.

The different types of comparison operators can be classified in the following categories:

- [Value comparisons][value comparisons] which compares values
- [Membership tests][membership test operations] which checks whether a value is present in some other object
- [Identity comparisons][identity comparisons] which checks whether two variables or values represent the same object

```{literalinclude} /../../../examples/pylint/w3601_bad_chained_comparison.py

```

## Syntax errors

(E0001)=

### Syntax Error (E0001)

1. _SyntaxError: Missing parentheses in call to 'print'_

   In Python 3, `print` is a builtin _function_, and should be called like any other function, with
   arguments inside parentheses. In previous versions of Python, `print` had been a keyword.

   ```{literalinclude} /../../../examples/syntax_errors/missing_parentheses_in_call_to_print.py

   ```

2. _SyntaxError: can't assign to literal_

   There must always be a variable on the left-hand side of the equals sign (where the term "
   variable" can refer to a single identifier `a = 10`, multiple identifiers `a, b = 10, 20`, a
   dictionary element `foo['a'] = 10`, a class attribute `foo.bar = 10`, etc.). We cannot assign to
   a string or numeric literal.

   ```{literalinclude} /../../../examples/syntax_errors/assignment_to_literal.py

   ```

3. _SyntaxError: invalid syntax_

   Some of the common causes of this error include:
   1. Missing colon at the end of an `if`, `elif`, `else`, `for`, `while`, `class`, or `def`
      statement.

      ```{literalinclude} /../../../examples/syntax_errors/missing_colon.py

      ```

   2. Assignment operator `=` used inside a condition expression (likely in place of the equality
      operator `==`).

      ```{literalinclude} /../../../examples/syntax_errors/assignment_inside_condition.py

      ```

   3. Missing quotation mark at the beginning or the end of a string literal.

      ```{literalinclude} /../../../examples/syntax_errors/missing_quote.py

      ```

   4. Assignment to a Python keyword.

      ```{literalinclude} /../../../examples/syntax_errors/assignment_to_keyword.py

      ```

      The following is a [list of Python keywords][keywords] which cannot be used as variable
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

   ```{literalinclude} /../../../examples/syntax_errors/undefined_operator.py

   ```

4. _IndentationError: unindent does not match any outer indentation level_

   We must use a constant number of whitespace characters for each level of indentation. If we start
   a code block using four spaces for indentation, we must use four spaces throughout that code
   block.

   ```{literalinclude} /../../../examples/syntax_errors/unindent_does_not_match_indentation.py

   ```

   Note that it is **strongly recommended** that we [**always use four spaces per indentation
   level**][pep8: indentation] throughout our code.

5. _IndentationError: unexpected indent_

   In Python, the only time we would increase the indentation level of our code is to define a new
   code block after a [compound statement][compound statements] such as `for`, `if`, `def`,
   or `class`.

   ```{literalinclude} /../../../examples/syntax_errors/unexpected_indent.py

   ```

(E0107)=

### Nonexistent operator (E0107)

This error occurs when we attempt to use C-style "pre-increment" or "pre-decrement" operators `++`
and `--`, which do not exist in Python.

```{literalinclude} /../../../examples/pylint/e0107_nonexistent_operator.py

```

Corrected version:

```python
spam = 0
spam += 1
spam -= 1
```

## Older errors

The following errors are no longer checked by the latest version of PythonTA.

(C0326)=

### Bad whitespace (C0326)

This error occurs when we include a wrong number of spaces around an operator, bracket, or block
opener. We should aim to follow
the [PEP8 convention on whitespace in expressions and statements][pep8: whitespace in expressions and statements]
.

(W0311)=

### Bad indentation (W0311)

This error occurs when an unexpected number of tabs or spaces is used to indent the code. It is
recommended that we use [_four spaces per indentation level_][pep8: indentation] throughout our
code.

(W0312)=

### Mixed indentation (W0312)

This error occurs when the code is indented with a mix of tabs and spaces. Please note that [_spaces
are the preferred indentation method_][pep8: tabs or spaces?].

(C0330)=

### Bad continuation (C0330)

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
[attributeerror]: https://docs.python.org/3/library/exceptions.html#AttributeError
[binary arithmetic operations]: https://docs.python.org/3/reference/expressions.html#binary-arithmetic-operations
[built-in functions]: https://docs.python.org/3/library/functions.html
[compound statements]: https://docs.python.org/3/reference/compound_stmts.html
[keywords]: https://docs.python.org/3/reference/lexical_analysis.html#keywords
[python documentation: baseexception]: https://docs.python.org/3/library/exceptions.html#BaseException
[python documentation: decorator]: https://docs.python.org/3/glossary.html#term-decorator
[python documentation: exception]: https://docs.python.org/3/library/exceptions.html#Exception
[python documentation: iterable]: https://docs.python.org/3/glossary.html#term-iterable
[python documentation: keyboardinterrupt]: https://docs.python.org/3/library/exceptions.html#KeyboardInterrupt
[python documentation: notimplemented]: https://docs.python.org/3/library/constants.html#NotImplemented
[python documentation: notimplementederror]: https://docs.python.org/3/library/constants.html#NotImplementedError
[python documentation: staticmethod]: https://docs.python.org/3/library/functions.html#staticmethod
[string and bytes literals]: https://docs.python.org/3/reference/lexical_analysis.html#string-and-bytes-literals
[unary arithmetic and bitwise operations]: https://docs.python.org/3/reference/expressions.html#unary-arithmetic-and-bitwise-operations
[value comparisons]: https://docs.python.org/3/reference/expressions.html#value-comparisons
[membership test operations]: https://docs.python.org/3/reference/expressions.html#membership-test-operations
[identity comparisons]: https://docs.python.org/3/reference/expressions.html#is-not
[dataclass fields]: https://docs.python.org/3/library/dataclasses.html#dataclasses.field

<!-- PEP8 -->

[pep8 imports]: https://www.python.org/dev/peps/pep-0008/#imports
[pep8: indentation]: https://www.python.org/dev/peps/pep-0008/#indentation
[pep8: naming conventions]: https://www.python.org/dev/peps/pep-0008/#naming-conventions
[pep8: other recommendations]: https://www.python.org/dev/peps/pep-0008/#other-recommendations
[pep8: tabs or spaces?]: https://www.python.org/dev/peps/pep-0008/#tabs-or-spaces
[pep8: whitespace in expressions and statements]: https://www.python.org/dev/peps/pep-0008/#whitespace-in-expressions-and-statements

<!-- StackOverflow -->

[stackoverflow: about the changing id of an immutable string]: https://stackoverflow.com/questions/24245324/about-the-changing-id-of-an-immutable-string
[stackoverflow: how to use the pass statement in python]: https://stackoverflow.com/a/22612774/2063031
[stackoverflow: what does 'super' do in python?]: https://stackoverflow.com/q/222877/2063031
[stackoverflow: what is the difference between `@staticmethod` and `@classmethod` in python?]: https://stackoverflow.com/questions/136097/what-is-the-difference-between-staticmethod-and-classmethod-in-python
[stackoverflow: when does python allocate new memory for identical strings?]: https://stackoverflow.com/questions/2123925/when-does-python-allocate-new-memory-for-identical-strings

<!-- everything else -->

[common gotchas - mutable default arguments]: http://docs.python-guide.org/en/latest/writing/gotchas/#mutable-default-arguments
[default parameter values in python]: http://effbot.org/zone/default-values.htm
[list comprehensions tutorial]: https://www.digitalocean.com/community/tutorials/understanding-list-comprehensions-in-python-3
[literally literals and other number oddities in python]: https://www.everymundo.com/literals-other-number-oddities-python/
[python double-under, double-wonder]: https://www.pixelmonkey.org/2013/04/11/python-double-under-double-wonder
[python's super considered harmful]: https://fuhm.net/super-harmful/
[super considered super!]: https://youtu.be/EiOglTERPEo
[the scope of index variables in python's for loops]: http://eli.thegreenplace.net/2015/the-scope-of-index-variables-in-pythons-for-loops/
[the story of none, true and false]: http://python-history.blogspot.ca/2013/11/story-of-none-true-false.html
[global variables are bad]: https://wiki.c2.com/?GlobalVariablesAreBad
