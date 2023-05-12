# Control Flow Graphs

This page describes an additional PythonTA feature: visualizing program control flow.
This feature makes it easier to visualize how the computer executes your program by producing a scalable control flow graph using the [graphviz] library.

## Sample Usage

This feature uses `python_ta.cfg.generate_cfg` to produce these control flow graphs.

It can be used to generate a control flow graph of the current file in which it is called.

```python
... # code here

if __name__ == "__main__":
    import python_ta.cfg

    python_ta.cfg.generate_cfg()
```

This feature is not limited to just the Python file containing the function call. It can also be used to generate a control flow graph of a different Python file. The set-up is the exact same as before, except we can pass an argument to the function call which is the relative path of the target file.

```python
... # same as before

python_ta.cfg.generate_cfg(<relative path of Python file>)
```

In either case, the output is a `.svg` file which shows the control flow of the program.

## API

```{eval-rst}
.. autofunction:: python_ta.cfg.generate_cfg
```

## Current Limitations

1. Various Python syntax such as Raise statements and for loops aren't labelled.

2. Only one control flow graph can be generated per function call (i.e. you can't pass in a list of files to generate control flow graphs for).

[graphviz]: https://github.com/graphp/graphviz
