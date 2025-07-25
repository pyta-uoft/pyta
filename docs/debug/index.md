# Loop, Recursion and Memory Tracing

This page describes two additional PythonTA features:

1. Print-based debugging for loops and recursion: This feature makes tracing easier by printing the state of each loop iteration or recursive function call in a nicely-formatted table using the [tabulate] library.
2. Snapshot-based debugging for visualizing the memory diagram: This feature makes it easier to visualize the Python memory model by leveraging the [MemoryViz](https://github.com/david-yz-liu/memory-viz) library.

These additional features are found in the `python.debug` submodule.

## Loop tracing with `AccumulationTable`

The following section will focus on the debugging of while and for loops.
This feature uses the `python_ta.debug.AccumulationTable` as a context manager wrapping a loop.
Let's start with two examples.

### Example 1: for loop

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

### Example 2: while loop

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

Finally, you can also specify the output format as a third attribute using the `format` argument. By default, the format is "table", which produces the same nicely formatted tabular output shown above. If you want to write the output as a .csv file, pass "csv" as the format.

For example, the following code writes a csv formattted output to `output.txt`.

```python
from python_ta.debug import AccumulationTable


def calculate_sum_and_averages(numbers: list) -> list:
    """Return the running sums and averages of the given numbers.
    """
    sum_so_far = 0
    list_so_far = []
    avg_so_far = None
    output_file = 'output.txt'
    with AccumulationTable(["sum_so_far", "avg_so_far", "list_so_far"], output=output_file, format='csv') as table:
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

## Recursion tracing with `RecursionTable`

This section will discuss the debugging of recursive functions.
This feature uses the `python_ta.debug.RecursionTable` class as a context manager wrapping a recursive function.

### Example usage

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
n    return value    called by
---  --------------  ------------
4    24              N/A
3    6               factorial(4)
2    2               factorial(3)
1    1               factorial(2)
0    1               factorial(1)
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

## Tracing with user-defined classes

Both `AccumulationTable` and `RecursionTable` call `str` on objects to display table entries.
If you plan to use instances of a user-defined class in these tables (for example, a `Tree` class when tracing a recursive `Tree` method), we recommend implementing the `__str__` method in your class to ensure a meaningful output is displayed.

### Current limitations

The `RecursionTable` is a new PythonTA feature and currently has the following known limitations:

1. `RecursionTable` uses [`sys.settrace`] to update variable state, and so is not compatible with other libraries (e.g. debuggers, code coverage tools).

2. Only one function can be traced per use of `RecursionTable`, and so mutually-recursive functions are not supported.

[tabulate]: https://github.com/astanin/python-tabulate
[`sys.settrace`]: https://docs.python.org/3/library/sys.html#sys.settrace

## Tracing the Python Memory Model

The following section will focus on tracing the Python memory model. This feature uses the `python_ta.debug.SnapshotTracer` as a context manager to visualize program memory.

### Example usage

```python
# demo.py
from python_ta.debug import SnapshotTracer


def func_multi_line(output_directory: str = None) -> None:
    """
    Function for testing SnapshotTracer
    """
    with SnapshotTracer(
        output_directory=output_directory,
        include_frames=("func_multi_line",),
        exclude_vars=("output_directory",),
        memory_viz_args=MEMORY_VIZ_ARGS,
    ):
        num = 123
        some_string = "Hello, world"
        num2 = 321
        arr = [some_string, "string 123321"]


if __name__ == '__main__':
    func_multi_line()
```

When this function runs, the variables within `func_multi_line` are captured, and memory models are outputted to `output_directory` for each line of code. For the expected output, refer to the snapshots in `tests/test_debug/snapshot_tracer_testing_snapshots/func_multi_line`.

### API

```{eval-rst}
.. automethod:: python_ta.debug.SnapshotTracer.__init__
```

### Current Limitations

The `SnapshotTracer` has the following limitations:

1. Due to differences in Python interpreters, this context manager only works with Python versions >= 3.10.
2. The context manager does not step into any function calls. Calling functions within the traced function may lead to undefined behavior.
3. `SnapshotTracer` uses [`sys.settrace`] to update variable states, and therefore is not compatible with other libraries (e.g., debuggers, code coverage tools).
