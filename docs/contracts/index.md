# Runtime Contract Checking

PythonTA supports runtime checking of type annotations, function preconditions, and class representation invariants.
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
The second, `check_contracts`, is a decorator allowing more fine-grained control over which
functions/classes have contract checking enabled.

```{eval-rst}
.. autofunction:: python_ta.contracts.check_all_contracts
```

```{eval-rst}
.. autofunction:: python_ta.contracts.check_contracts(func_or_class)
```

Finally, you can set the `DEBUG_CONTRACTS` constant to `True` to enable debugging information to be printed when checking contracts.

```{eval-rst}
.. autodata:: python_ta.contracts.DEBUG_CONTRACTS
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

### Functions: custom preconditions

You can write arbitrary preconditions as Python expressions in the function docstring, using the following syntax:

```
Preconditions:
    - <expr>
    - <expr>
    - <expr>
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
2. Whenever an attribute is reassigned *outside* a method of the class.

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

Similar to function preconditions, you can define *representation invariants* within a class docstring.
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

## Technical notes

This section describes some more technical features of PythonTA's contract checking. 

### Scope

All custom preconditions and representations are evaluated in the scope where their enclosing function/class is defined.
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
Attribute type annotations and representation invariants are checked based on the *reverse* method resolution order of their classes.
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
