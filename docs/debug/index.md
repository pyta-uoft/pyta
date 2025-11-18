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

### Example 3: Multiple sequential loops

The `AccumulationTable` context manager can track multiple sequential loops within the same `with` block. Each loop will generate its own separate table in the output.

```python
# demo.py
from python_ta.debug import AccumulationTable


def process_with_multiple_loops(numbers: list) -> int:
    """Process numbers through multiple sequential loops.
    """
    sum_so_far = 0
    i = 0
    with AccumulationTable(["sum_so_far", "i"]):
        for number in numbers:
            sum_so_far = sum_so_far + number
        for j in range(len(numbers)):
            sum_so_far += 1
        while i < 5:
            i += 1
            sum_so_far -= i

    return sum_so_far


if __name__ == '__main__':
    result = process_with_multiple_loops([10, 20, 30])
```

When this file is run, we get the following output showing three separate tables (one for each loop):

```console
$ python demo.py

iteration    number    sum_so_far    i
-----------  --------  ------------  ---
0            N/A       0             0
1            10        10            0
2            20        30            0
3            30        60            0


iteration    j    sum_so_far    i
-----------  ---  ------------  ---
0            N/A  60            0
1            0    61            0
2            1    62            0
3            2    63            0


iteration    sum_so_far    i
-----------  ------------  ---
0            63            0
1            62            1
2            60            2
3            57            3
4            53            4
5            48            5
```

### API

```{eval-rst}
.. automethod:: python_ta.debug.AccumulationTable.__init__
```

The `AccumulationTable` class provides a `loops` instance attribute that becomes available after the `with` statement.

```{eval-rst}
.. autoattribute:: python_ta.debug.AccumulationTable.loops
```

This is a list of dictionaries, where each dictionary contains data for one loop:

- `table.loops[i]["loop_variables"]`: A dictionary mapping loop variable names to their values during each iteration
- `table.loops[i]["loop_accumulators"]`: A dictionary mapping accumulator names to their values during each iteration
- `table.loops[i]["loop_lineno"]`: The line number of the loop in the source code

For example, to access data from a single loop:

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

    # Access the first (and only) loop's data
    print(table.loops[0]["loop_accumulators"])
    print(table.loops[0]["loop_variables"])
    return list_so_far

```

For multiple sequential loops, you can access each loop's data separately:

```python
from python_ta.debug import AccumulationTable


def process_with_multiple_loops(numbers: list) -> int:
    """Process numbers through multiple sequential loops.
    """
    sum_so_far = 0
    i = 0
    with AccumulationTable(["sum_so_far", "i"]) as table:
        for number in numbers:
            sum_so_far = sum_so_far + number
        for j in range(len(numbers)):
            sum_so_far += 1
        while i < 5:
            i += 1
            sum_so_far -= i

    # Access data from each loop
    print("First loop:", table.loops[0]["loop_accumulators"])
    print("Second loop:", table.loops[1]["loop_accumulators"])
    print("Third loop:", table.loops[2]["loop_accumulators"])

    return sum_so_far

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

2. Nested loops may not be tracked accurately. The `AccumulationTable` is designed to work best with multiple sequential loops (loops that run one after another), not with loops nested inside other loops.

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
