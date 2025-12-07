"""
Table data structure that prints a nicely formatted table
for an accumulator loop
"""

from __future__ import annotations

import copy
import csv
import inspect
import sys
from typing import TYPE_CHECKING, Any, Generator, Literal, Optional, Union

import astroid
import tabulate
from astroid.nodes import (
    AssignName,
    For,
    Module,
    NodeNG,
    While,
)

if TYPE_CHECKING:
    import types

NO_VALUE = "N/A"


def num_whitespaces(start_of_loop: str) -> int:
    """Return the number of spaces at the beginning of the accumulation loop"""
    blank_chars = 0
    for char in start_of_loop:
        if char.isspace():
            blank_chars += 1
        else:
            break

    return blank_chars


def get_with_lines(lines: list[str], num_whitespace: int) -> str:
    """Return the lines in the with block"""
    endpoint = len(lines)
    for i in range(len(lines)):
        if lines[i].strip() != "" and not lines[i][num_whitespace].isspace():
            endpoint = i
            break

    return "\n".join(lines[:endpoint])


def _is_nested_loop(node: NodeNG, with_module: Module) -> bool:
    """Helper checks the ancestor chain of a given loop node (For or While) to check if it is nested within the context
    manager."""
    curr_node = node
    while curr_node.parent is not None and curr_node.parent is not with_module:
        if isinstance(curr_node.parent, (For, While)):
            return True
        curr_node = node.parent
    return False


def get_loop_nodes(frame: types.FrameType) -> Generator[Union[For, While]]:
    """Yield the For or While node(s) from the frame containing the accumulator loop(s)"""
    func_string = inspect.cleandoc(inspect.getsource(frame))
    with_stmt_index = inspect.getlineno(frame) - frame.f_code.co_firstlineno
    lst_str_lines = func_string.splitlines()
    lst_from_with_stmt = lst_str_lines[with_stmt_index + 1 :]
    num_whitespace = num_whitespaces(lst_str_lines[with_stmt_index])
    with_lines = get_with_lines(lst_from_with_stmt, num_whitespace)

    with_module = astroid.parse(with_lines)
    for statement in with_module.nodes_of_class((For, While)):
        if isinstance(statement, (For, While)) and not _is_nested_loop(statement, with_module):
            yield statement


class AccumulationTable:
    """
    Class used as a form of print debugging to analyze different loop and
    accumulation variables during each iteration in a for or while loop

    Instance attributes:
        loop_accumulators: a mapping between the accumulation variables. Read-only access and only works with a single
            loop in context manager.
        loop_variables: a mapping between the loop variables and their values during each iteration. Read-only access
            and only works with a single loop in context manager.
        _accumulator_names: either a list of accumulator variable names to track across all loops,
            or a list of lists where each inner list contains the accumulator names for the corresponding loop
        loops: a list of dictionaries, one per loop, each containing:
            - "loop_variables": dict mapping loop variable names to their values per iteration
            - "loop_lineno": the line number of the loop
            - "loop_accumulators": dict mapping accumulator names to their values per iteration
        output_filepath: the filepath where the table will be written if it is passed in, defaults to None
        output_format: the format of the output ("table" or "csv")
    """

    _accumulator_names: Union[list[str], list[list[str]]]
    """Either a list of accumulator variable names to track across all loops,
    or a list of lists where each inner list contains the accumulator names for the corresponding loop."""
    loops: list[dict[str, Any]]
    """A list of dictionaries containing loop-specific data for each loop in the with block."""
    output_filepath: Optional[str]
    output_format: str

    def __init__(
        self,
        accumulation_names: Union[list[str], list[list[str]]],
        output: Union[None, str] = None,
        format: Literal["table", "csv"] = "table",
    ) -> None:
        """Initialize an AccumulationTable context manager for print-based loop debugging.

        Args:
            accumulation_names: either a list of accumulator variable names to track across all loops,
                or a list of lists where each inner list contains the accumulator names for the corresponding loop.
            output: optional filepath where the table will be written. If None, prints to stdout.
            format: output format, either "table" (formatted table) or "csv" (CSV format).
        """
        self._accumulator_names = accumulation_names
        self.loops = []
        self.output_filepath = output
        self.output_format = format

    @property
    def loop_accumulators(self) -> dict[str, list]:
        """Read-only access to accumulator values. Only works with a single loop in context manager."""
        if len(self.loops) == 1:
            return self.loops[0]["loop_accumulators"]
        raise ValueError("Only available when tracking a single loop")

    @property
    def loop_variables(self) -> dict[str, list]:
        """Read-only access to loop variable values. Only works with a single loop in context manager."""
        if len(self.loops) == 1:
            return self.loops[0]["loop_variables"]
        raise ValueError("Only available when tracking a single loop")

    def _record_iteration(self, frame: types.FrameType, lst_index: int) -> None:
        """Record the values of the accumulator variables and loop variables of an iteration for a given loop at index
        lst_index."""
        loop_variables = self.loops[lst_index]["loop_variables"]
        loop_accumulators = self.loops[lst_index]["loop_accumulators"]
        if loop_variables and len(list(loop_variables.values())[0]) > 0:
            for loop_var in loop_variables:
                loop_variables[loop_var].append(copy.deepcopy(frame.f_locals[loop_var]))
        else:
            for loop_var in loop_variables:
                loop_variables[loop_var].append(NO_VALUE)

        for accumulator in loop_accumulators.keys():
            if accumulator in frame.f_locals:
                value = copy.deepcopy(frame.f_locals[accumulator])
            elif accumulator in frame.f_code.co_varnames or accumulator in frame.f_code.co_names:
                value = NO_VALUE
            else:
                # name error wil be raised if accumulator cannot be found
                try:
                    value = eval(accumulator, frame.f_globals, frame.f_locals)
                except NameError as e:
                    if sys.version_info >= (3, 10) and e.name in loop_variables:
                        value = NO_VALUE
                    else:
                        raise
                else:
                    value = copy.deepcopy(value)

            loop_accumulators[accumulator].append(value)

    def _create_iteration_dict(self, lst_index: int) -> dict:
        """Return a dictionary that maps each accumulator and loop variable to its respective value during each
        iteration for a given loop at index `lst_index`."""
        loop_variables = self.loops[lst_index]["loop_variables"]
        loop_accumulators = self.loops[lst_index]["loop_accumulators"]
        iteration = None

        if loop_variables:
            iteration = list(range(len(list(loop_variables.values())[0])))
        elif loop_accumulators:
            iteration = list(range(len(list(loop_accumulators.values())[0])))

        return {
            "iteration": iteration,
            **loop_variables,
            **loop_accumulators,
        }

    def _tabulate_data(self) -> None:
        """Print the values of the accumulator and loop variables into a table"""
        if self.output_filepath is None:
            file_io = sys.stdout
        else:
            try:
                file_io = open(self.output_filepath, "a", newline="")
            except OSError as e:
                print(f"Error opening output file: {e}")
                return

        try:
            for lst_index in range(len(self.loops)):
                iteration_dict = self._create_iteration_dict(lst_index)
                if self.output_format == "table":
                    table = tabulate.tabulate(
                        iteration_dict,
                        headers="keys",
                        colalign=(*["left"] * len(iteration_dict),),
                        disable_numparse=True,
                        missingval="None",
                    )
                    if lst_index > 0:
                        file_io.write("\n")
                    file_io.write(table)
                    file_io.write("\n")
                else:
                    csv_preformat = [
                        dict(zip(iteration_dict.keys(), row))
                        for row in zip(*iteration_dict.values())
                    ]
                    writer = csv.DictWriter(file_io, fieldnames=iteration_dict.keys())
                    writer.writeheader()
                    writer.writerows(csv_preformat)
        except OSError as e:
            print(f"Error writing data: {e}")
        finally:
            if self.output_filepath is not None:
                file_io.close()

    def _trace_loop(self, frame: types.FrameType, event: str, _arg: Any) -> None:
        """Trace through the loop and store the values of the
        accumulators and loop variable during each iteration
        """
        if event == "line":
            for i, loop in enumerate(self.loops):
                if frame.f_lineno == loop["loop_lineno"]:
                    self._record_iteration(frame, i)
                    break  # Loop has been found, can safely break

    def _setup_table(self) -> None:
        """
        Get the frame of the code containing the with statement, cut down the source code
        such that it only contains the with statement and the accumulator loop(s) and set up
        the trace function to track the values of the accumulator variables for the loop(s) during each iteration.
        """
        func_frame = inspect.getouterframes(
            inspect.getouterframes(inspect.currentframe())[1].frame
        )[1].frame

        nodes = list(get_loop_nodes(func_frame))

        if self._accumulator_names and isinstance(self._accumulator_names[0], list):
            assert len(self._accumulator_names) == len(nodes), (
                f"Number of accumulator lists ({len(self._accumulator_names)}) "
                f"must match number of loops ({len(nodes)})"
            )

        for i, node in enumerate(nodes):
            loop_lineno = inspect.getlineno(func_frame) + node.lineno
            loop_variables = {}

            if isinstance(node, For):
                loop_variables = {
                    nested_node.name: [] for nested_node in node.target.nodes_of_class(AssignName)
                }

            # Determine accumulators for this specific loop
            if self._accumulator_names and isinstance(self._accumulator_names[0], list):
                accumulators_for_this_loop = self._accumulator_names[i]
            else:
                accumulators_for_this_loop = self._accumulator_names

            assert (
                accumulators_for_this_loop or loop_variables
            ), "The loop accumulator and loop variables cannot be both empty"

            self.loops.append(
                {
                    "loop_variables": loop_variables,
                    "loop_lineno": loop_lineno,
                    "loop_accumulators": {acc: [] for acc in accumulators_for_this_loop},
                }
            )

        func_frame.f_trace = self._trace_loop
        sys.settrace(lambda *_args: None)

    def __enter__(self) -> AccumulationTable:
        """Set up and return the accumulation table for the accumulator loop"""
        self._setup_table()
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        """Exit the with block, disable tracing, and print the table(s) for all tracked loops"""
        sys.settrace(None)
        inspect.getouterframes(inspect.currentframe())[1].frame.f_trace = None
        self._tabulate_data()
