# Loop and Recursive Debugging

This page describes an additional PythonTA feature: print-based debugging for loops and recursion.
This feature makes tracing easier by printing the state of each iteration or call in a nicely-formatted table using the [tabulate] library.

## Loops

The following section will focus on the debugging of while and for loops.

### Example usage

This feature uses the `python_ta.debug.AccumulationTable` as a context manager wrapping a loop.

#### For loop example

```python
# demo.py
from python_ta.debug import AccumulationTable


def calculate_sum_and_averages(numbers: list) -> list:
    """Return the running sums and averages of the given numbers.
    """
    sum_so_far = 0
    list_so_far = []
    avg_so_far = None
    with AccumulationTable(["sum_so_far", "avg_so_far", "list_so_far"]):
        for number in numbers:
            sum_so_far = sum_so_far + number
            avg_so_far = sum_so_far / (len(list_so_far) + 1)
            list_so_far.append((sum_so_far, avg_so_far))

    return list_so_far


if __name__ == '__main__':
    calculate_sum_and_averages([10, 20, 30, 40, 50, 60])
```

When this file is run, we get the following output:

```console
$ python demo.py
iteration    number    sum_so_far    avg_so_far    list_so_far
-----------  --------  ------------  ------------  ---------------------------------------------------------------------------
0            N/A       0             None          []
1            10        10            10.0          [(10, 10.0)]
2            20        30            15.0          [(10, 10.0), (30, 15.0)]
3            30        60            20.0          [(10, 10.0), (30, 15.0), (60, 20.0)]
4            40        100           25.0          [(10, 10.0), (30, 15.0), (60, 20.0), (100, 25.0)]
5            50        150           30.0          [(10, 10.0), (30, 15.0), (60, 20.0), (100, 25.0), (150, 30.0)]
6            60        210           35.0          [(10, 10.0), (30, 15.0), (60, 20.0), (100, 25.0), (150, 30.0), (210, 35.0)]
```

#### While loop example

To use `AccumulationTable` with while loops, you need to pass in the name of the loop variable when initializing the table.

```python
# demo.py
from python_ta.debug import AccumulationTable


def calculate_sum_up_to_target(target: int) -> list:
    """Return the running sums of the given target.
    """
    number = 0
    sum_so_far = 0
    list_so_far = []
    with AccumulationTable(["number", "sum_so_far", "list_so_far"]):
        while number <= target:
            sum_so_far = sum_so_far + number
            list_so_far = list_so_far + [number]
            number += 1

    return list_so_far


if __name__ == '__main__':
    calculate_sum_up_to_target(5)
```

When this file is run, we get the following output:

```console
$ python demo.py
iteration    number    sum_so_far    list_so_far
-----------  --------  ------------  ------------------
0            0         0             []
1            1         0             [0]
2            2         1             [0, 1]
3            3         3             [0, 1, 2]
4            4         6             [0, 1, 2, 3]
5            5         10            [0, 1, 2, 3, 4]
6            6         15            [0, 1, 2, 3, 4, 5]
```

### API

```{eval-rst}
.. automethod:: python_ta.debug.AccumulationTable.__init__
```

The `AccumulationTable` class has the following instance attributes you can access after the `with` statement.

```{eval-rst}
.. autoattribute:: python_ta.debug.AccumulationTable.loop_variables

.. autoattribute:: python_ta.debug.AccumulationTable.loop_accumulators
```

For example:

```python
from python_ta.debug import AccumulationTable


def calculate_sum_and_averages(numbers: list) -> list:
    """Return the running sums and averages of the given numbers.
    """
    sum_so_far = 0
    list_so_far = []
    avg_so_far = None
    with AccumulationTable(["sum_so_far", "avg_so_far", "list_so_far"]) as table:
        for number in numbers:
            sum_so_far = sum_so_far + number
            avg_so_far = sum_so_far / (len(list_so_far) + 1)
            list_so_far.append((sum_so_far, avg_so_far))

    print(table.loop_accumulators)
    return list_so_far

```

You also have the option to pass in a file path as an attribute to the AccumulationTable object. In this case, the table will be appended to the file instead of being written the console.
For example:

```python
from python_ta.debug import AccumulationTable


def calculate_sum_and_averages(numbers: list) -> list:
    """Return the running sums and averages of the given numbers.
    """
    sum_so_far = 0
    list_so_far = []
    avg_so_far = None
    output_file = 'output.txt'
    with AccumulationTable(["sum_so_far", "avg_so_far", "list_so_far"], output_file) as table:
        for number in numbers:
            sum_so_far = sum_so_far + number
            avg_so_far = sum_so_far / (len(list_so_far) + 1)
            list_so_far.append((sum_so_far, avg_so_far))

    return list_so_far
```

## Current limitations

The `AccumulationTable` is a new PythonTA feature and currently has the following known limitations:

1. `AccumulationTable` uses [`sys.settrace`] to update variable state, and so is not compatible with other libraries (e.g. debuggers, code coverage tools).

2. The `AccumulationTable` context manager can only log the execution of one for loop.
   To log the state of multiple for loops, each must be wrapped in a separate `with` statement and fresh `AccumulationTable` instance.

## Recursion

This section will discuss the debugging of recursive functions.

### Example usage

This feature uses the `python_ta.debug.RecursionTable` as a context manager wrapping a recursive function.

```python
# demo.py
from python_ta.debug import RecursionTable

def factorial(n: int) -> int:
    """Calculate the factorial of n."""
    if n == 0:
        return 1
    return n * factorial(n - 1)

def trace_factorial(number: int) -> None:
    "Trace a recursively defined factorial function using RecursionTable."
    with RecursionTable("factorial"):
        factorial(number)

if __name__ == '__main__':
    trace_factorial(4)
```

When this file is run, we get the following output:

```console
$ python demo.py
n    called by     return value
---  ------------  --------------
4    N/A           24
3    factorial(4)  6
2    factorial(3)  2
1    factorial(2)  1
0    factorial(1)  1
```

### API

```{eval-rst}
.. automethod:: python_ta.debug.RecursionTable.__init__
```

The `RecursionTable` class has the following methods you can access after the `with` statement.

```{eval-rst}
.. automethod:: python_ta.debug.RecursionTable.get_recursive_dict
```

For example:

```python
# demo.py
from python_ta.debug import RecursionTable

def factorial(n: int) -> int:
    """Calculate the factorial of n."""
    if n == 0:
        return 1
    return n * factorial(n - 1)

def trace_factorial(number: int) -> None:
    "Trace a recursively defined factorial function using RecursionTable."
    with RecursionTable("factorial") as table:
        factorial(number)

    traced_data = table.get_recursive_dict()
    print(traced_data)

```

### Current limitations

The `RecursionTable` is a new PythonTA feature and currently has the following known limitations:

1. `RecursionTable` uses [`sys.settrace`] to update variable state, and so is not compatible with other libraries (e.g. debuggers, code coverage tools).

2. Recursive instance methods are not meaningfully traced as the `self` parameter is a custom object and needs to be processed accordingly.

[tabulate]: https://github.com/astanin/python-tabulate
[`sys.settrace`]: https://docs.python.org/3/library/sys.html#sys.settrace
