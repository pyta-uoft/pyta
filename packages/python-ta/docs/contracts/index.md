# Runtime Contract Checking

PythonTA supports runtime checking of type annotations, function preconditions, function postconditions, and class representation invariants.
In contrast to the [checkers from Pylint and our own custom checkers](../checkers/index), the checks described in this section execute when your code is run.
This makes it easy to incorporate these checks when executing, debugging, and testing your code.

## Quick demo

Here is a minimal example of using the `python_ta.contracts` module to check a function's preconditions.

```python
# demo.py
def divide(x: int, y: int) -> int:
    """Return x // y.

    Preconditions:
        - y != 0
    """
    return x // y


if __name__ == '__main__':
    from python_ta.contracts import check_all_contracts
    check_all_contracts()

    divide(10, 0)  # Preconditions on y violated
```

If we run this file, an `AssertionError` is raised when we call `divide(10, 0)`:

```console
$ python demo.py
Traceback (most recent call last):
  ...
AssertionError: divide precondition "y != 0" violated for arguments {'x': 10, 'y': 0}.
```

Similarly, violating a parameter's type annotation also raises an error:

```pycon
>>> from demo import divide
>>> divide(10, '2')
Traceback (most recent call last):
  File "<stdin>", line 1, in <module>
  ...
AssertionError: divide argument '2' did not match type annotation for parameter "y: <class 'int'>"
```

## API

The `python_ta.contracts` module offers two functions for enabling contract checking.
The first, `check_all_contracts`, enables contract checking for all functions and classes defined within a module or set of modules.
The second, `check_contracts`, is a decorator allowing more fine-grained control over which functions/classes have contract checking enabled.

```{eval-rst}
.. autofunction:: python_ta.contracts.check_all_contracts
```

```{eval-rst}
.. autofunction:: python_ta.contracts.check_contracts(func_or_class)
```

You can pass an object into the function `validate_invariants` to manually check the representation invariants of the object.

```{eval-rst}
.. autofunction:: python_ta.contracts.validate_invariants(object)
```

You can set the `ENABLE_CONTRACT_CHECKING` constant to `True` to enable all contract checking.

```{eval-rst}
.. autodata:: python_ta.contracts.ENABLE_CONTRACT_CHECKING
```

You can set the `STRICT_NUMERIC_TYPES` constant to `False` to allow more specific numeric types to be accepted by more general type annotations, as described in [PEP 484](https://peps.python.org/pep-0484/#the-numeric-tower). For example, this allows `int` values to be accepted by `float` type annotations.

```{eval-rst}
.. autodata:: python_ta.contracts.STRICT_NUMERIC_TYPES
```

You can set the `DEBUG_CONTRACTS` constant to `True` to enable debugging information to be printed when checking contracts.

```{eval-rst}
.. autodata:: python_ta.contracts.DEBUG_CONTRACTS
```

The following constant is used to make contract checking compatible with PyCharm's "Run File in Python Console" action.

```{eval-rst}
.. autodata:: python_ta.contracts.RENAME_MAIN_TO_PYDEV_UMD
```

## Command Line Interface

The `python_ta.contracts` CLI can execute a file as `__main__` with contracts enabled.

The utmost basic usage of this command is with `python -m python_ta.contracts FILE` where `FILE`
is the executed Python script such as `demo.py`. See `python -m python_ta.contracts --help` for the full list of
arguments and options. (Note that you may have to write `python3 -m` depending on your installation)

```{note}
The `python_ta.contracts` CLI command will search the main script for where to begin checking contracts from.
This search will only find if blocks that are one line and written like `if __name__ == '__main__':`,
while also accepting varying quotations and whitespaces. Any scripts with an unsupported
variation of this if condition will not be recognized nor run.
```

## Specifying contracts

This sections describes the different kinds of contract specifications that PythonTA currently supports.

### Functions: type annotations

PythonTA will verify all function parameter and return type annotations specified following the standard in [PEP484](https://www.python.org/dev/peps/pep-0484/):

```python
def f(x0: type0, x1: type1 ...) -> return_type:
```

Whenever the function is called, parameter types are checked before executing the function body, and the return type is checked immediately before the function returns.
PythonTA uses the [typeguard] library to check types.

(functions-custom-preconditions)=

### Functions: custom preconditions

You can write arbitrary preconditions as Python expressions in the function docstring, using the following syntax.
Multi-line preconditions can be created by using a backslash ('\') following a space at the end of each line except the last:

```
Preconditions:
    - <expr>
    - <expr>
    - <expr> \
      <expr> \
      <expr>
```

Each expression is evaluated in the same scope as the function body, in top-down order.
If any of the expressions evaluate to a falsey value, an `AssertionError` is raised.
A precondition expression can be followed by a comment using `#`.

PythonTA ignores expressions that cannot be parsed as valid Python code, or that raise an error when they are evaluated.
When `DEBUG_CONTRACTS` is `True`, PythonTA will print a warning message when it encounters either of these situations.

Examples:

```python
from python_ta.contracts import check_contracts


@check_contracts
def divide(x: int, y: int) -> int:
    """Return x // y.

    Preconditions:
        - y != 0
    """
    return x // y


@check_contracts
def divide_each(lst1: list[int], lst2: list[int]) -> list[int]:
    """Return the quotient of each number in lst1 divided by the corresponding number in lst2.

    Preconditions:
        - len(lst1) == len(lst2)
        - all(n != 0 for n in lst2)
    """
    return [x // y for x, y in zip(lst1, lst2)]
```

```{note}
Type annotations are evaluated before these precondition expressions, and so when you are
writing custom preconditions you can assume that the parameters have the correct type.
```

### Functions: custom postconditions

Postconditions for a function can be specified much like preconditions in the function docstring.
Multi-line postconditions can be created by using a backslash ('\') following a space at the end of each line except the last:

```
Postconditions:
    - <expr>
    - <expr>
    - <expr> \
      <expr> \
      <expr>
```

One interesting thing to note about postcondition expressions is that they can include the identifier `$return_value`, which is used to refer to the return value of the function.
Thus, each `<expr>` in the snippet above can refer to the return value of the function through `$return_value`, in addition to any
other variables and identifiers that are in scope for the function.

Aside from the usage and availability of the `$return_value` identifier, function postconditions are handled the same way as [function preconditions](#functions-custom-preconditions).

Examples:

```python
from python_ta.contracts import check_contracts


@check_contracts
def non_negative_sum(x: int, y: int) -> int:
    """Return x + y. If x + y < 0, then return 0 instead.

    Postconditions:
        - $return_value >= 0
    """
    return max(0, x + y)


@check_contracts
def non_negative_sum_each(lst1: list[int], lst2: list[int]) -> list[int]:
    """Return a list of non-negative sums when a number in lst1 is added to the corresponding number in lst2.
    If the sum is negative for a pair, then it is taken to be 0 for that pair.

    Preconditions:
        - len(lst1) == len(lst2)
    Postconditions:
        - all(num >= 0 for num in $return_value)
    """
    return [non_negative_sum(x, y) for x, y in zip(lst1, lst2)]
```

```{note}
Postcondition expressions are evaluated after the type check on the return type is complete. Thus, you can assume that
the return value of the function has the correct type when postcondition expressions are evaluated.
```

### Classes: methods

Because all methods are functions, PythonTA will also check type annotations and preconditions for methods.

```{note}
While it is possible to use the `check_contracts` decorator on an individual method in a class, we strongly recommend using the decorator on the entire class.
This will enable contract checking for all methods in the class, and the additional checks for instance attributes and representation invariants described below.
```

### Classes: attribute types

Both instance attributes and class attributes can have type annotations specified within a class definition, using the following syntax:

```python
class A:
    attr0: type0
    attr1: type1
    ...
```

When contract checking is enabled for the class, these attribute types are checked (using [typeguard]) at the following times:

1. After every method call.
2. Whenever an attribute is reassigned _outside_ a method of the class.

Examples:

```python
from python_ta.contracts import check_contracts


@check_contracts
class Person:
    """A class representing a person.
    """
    age: int
    name: str

    def __init__(self, name: str, age: int) -> None:
        """Initialize a new person.
        """
        self.name = name
        self.age = age

    def set_age_incorrectly(self) -> None:
        """Set this person's age to a string value."""
        self.age = str(self.age)


if __name__ == '__main__':
    # Create a new Person; name and age types are checked at end of __init__
    p = Person('David', 100)

    # Types are checked after this method call; AssertionError is raised
    p.set_age_incorrectly()

    # Types are checked when attribute is reassigned; AssertionError is raised
    p.name = 100
```

````{note}
Other static analysis tools and IDEs understand instance attribute type annotations specified within the initializer,
e.g.

```python
class A:
    def __init__(self) -> None:
        self.a : int = 10
```

However, PythonTA currently does *not* support this syntax; all attributes must have their type annotations specified at the top level of the class body.
````

### Classes: custom representation invariants

Similar to function preconditions, you can define _representation invariants_ within a class docstring.
Each representation invariant is a Python expression involving one or more attributes, and are defined using the following syntax:

```
Representation Invariants:
    - <expr>
    - <expr>
    - <expr>
```

Representation invariants are checked after method calls and when attributes are reassigned, immediately after attribute types are checked.
Aside from when they are checked, representation invariants are handled the same way as [function preconditions](#functions-custom-preconditions).

Examples:

```python
from python_ta.contracts import check_contracts


@check_contracts
class Person:
    """A class representing a person.

    Representation Invariants:
        - self.name.isalpha()
        - self.age >= 0
    """
    age: int
    name: str

    def __init__(self, name: str, age: int) -> None:
        """Initialize a new person.
        """
        self.name = name
        self.age = age

    def decrease_age(self) -> None:
        """Subtract 100 from this person's age."""
        self.age -= 100


if __name__ == '__main__':
    # Create a new Person; representation invariants are checked at end of __init__
    p = Person('David', 10)

    # Representation invariants are checked after this method call; AssertionError is raised
    p.decrease_age()

    # Representation invariants are checked when attribute is reassigned; AssertionError is raised
    p.name = '123'
```

## Disabling checks

When used on functions, the four optional boolean arguments (`arguent_types`, `return_type`, `preconditions`, `postconditions`) can be used to selectively disable contract checking.
By default, all checks are enabled; assigning `False` to any of these parameters suppresses its related check. When used on classes, the parameters have no effect.

**Example: Disabling a single check**

```python
from python_ta.contracts import check_contracts

@check_contracts(preconditions=False)
def safe_divide(x: int, y: int) -> float:
    """Return x / y.

    Preconditions:
        - y != 0
    """
    # Preconditions check will not be enforced
    return x / y
```

**Example 2: Disable all contract checks**

```python
from python_ta.contracts import check_contracts

@check_contracts(argument_types=False,
                 return_type=False,
                 preconditions=False,
                 postconditions=False)
def add(x: int, y: int) -> int:
    """Return x + y.

    Preconditions:
        - isinstance(x, int)
        - isinstance(y, int)
    Postconditions:
        - $return_value >= x
    """
    # None of the above checks will be enforced
    return x + y
```

## Technical notes

This section describes some more technical features of PythonTA's contract checking.

### Scope

All custom preconditions, postconditions, and representations are evaluated in the scope where their enclosing function/class is defined.
Here is an example where a function's preconditions refer to both a helper function defined in the same module, and one that's been imported from a separate module.

```python
from math import sqrt
from python_ta.contracts import check_contracts


@check_contracts
def f(x: float, y: float) -> float:
    """Return x + y.

    Preconditions:
        - x >= 0
        - sqrt(x) >= 3.5
        - is_small(y)
    """
    return x + y


def is_small(y: float) -> bool:
    """Return whether the absolute value of y is less than 1."""
    return abs(y) < 1


if __name__ == '__main__':
    # This raises an AssertionError: sqrt(x) >= 3.5 is False
    f(1, 0)

    # This also raises an AssertionError: is_small(y) is False
    f(100, 2)
```

```{warning}
The above example illustrates a currently limitation of PythonTA: the `sqrt` function must be imported
so that it is in scope for the precondition, even though the function isn't called in the program code.
This causes some code checking tools (including PythonTA) to report an "unused import" error for the function.
```

### Inheritance

A subclass "inherits" the attribute type annotations and representation invariants of its superclass(es).
That is, when contract checking is enabled on a class, PythonTA will check not just the attribute type annotations and representation invariants defined within the class, but within all of its superclasses as well.

Examples:

```python
from python_ta.contracts import check_contracts


@check_contracts
class Person:
    """A class representing a person.

    Representation Invariants:
      - self.age > 0
      - self.name.isalpha()
    """
    age: int
    name: str

    def __init__(self, name: str, age: int) -> None:
        """Initialize a new person.
        """
        self.name = name
        self.age = age


@check_contracts
class Student(Person):
    """A class representing a student.

    Representation Invariants:
      - len(self.id) == 8
    """
    id: str

    def __init__(self, name: str, age: int, id_: str) -> None:
        """Initialize a new student.
        """
        super().__init__(name, age)
        self.id = id_


if __name__ == '__main__':
    s = Student('David', 20, '01234567')

    # Each of the following attribute assignments fail, violating one of the type annotations
    # or representation invariants in Student or Person.
    s.name = 10
    s.name = ''

    s.age = '10'
    s.age = -1

    s.id = 10
    s.id = ''
```

All attribute type annotations are checked before all representation invariants.
Attribute type annotations and representation invariants are checked based on the _reverse_ method resolution order of their classes.
So in the above example, the order of checks made is:

1. `self.age` is an `int`
2. `self.name` is a `str`
3. `self.id` is a `str`
4. `self.age > 0`
5. `self.name.isalpha()`
6. `len(self.id) == 8`

[typeguard]: https://github.com/agronholm/typeguard

### Partial Initialization

Post-condition checks on class attribute types and representation invariants are disabled while
initializing an instance of a class. Due to the nature of the approach to disabling these checks,
you may encounter that these checks will not run if you pass an already-created instance of an object
through an externally defined function named `__init__` whose first parameter is self.

```python
class DataClass:
    """
    Representation Invariants:
    - self.my_int > 10

    """
    my_int: int

    def __init__(self) -> None:
        self.my_int = 30

    def annotation_violation(self) -> None:
        """
        Should throw a type annotation error with an int attribute being given a string
        """
        self.my_int = 0


class UnrelatedClass:
    def __init__(self) -> None:
        DataClass.annotation_violation(self)


if __name__ == '__main__':
    import python_ta.contracts
    python_ta.contracts.check_all_contracts()

    my_instance = DataClass()
    try:
        my_instance.annotation_violation()
    except AssertionError:
        print('Properly raised AssertionError')
    else:
        print('Did not raise AssertionError')

    my_instance2 = DataClass()
    try:
        UnrelatedClass.__init__(my_instance2)
    except AssertionError:
        print('Properly raised AssertionError')
    else:
        print('Did not raise AssertionError')
```

The above example outputs the following

```
>>> Properly raised AssertionError
>>> Did not raise AssertionError
```
