"""
Table data structure that prints a nicely formatted table
for an accumulator loop
"""
from __future__ import annotations

import copy
import inspect
import sys
import types
from typing import Any

import astroid
import tabulate


def num_whitespaces(start_of_loop: str) -> int:
    """Return the number of spaces at the beginning of the accumulation loop"""
    blank_chars = 0
    for char in start_of_loop:
        if char.isspace():
            blank_chars += 1
        else:
            break

    return blank_chars


def get_loop_lines(lines: list[str], num_whitespace: int) -> str:
    """Return the lines from the start to the end
    of the accumulator loop
    """
    endpoint = len(lines)
    for i in range(len(lines)):
        if lines[i].strip() != "" and not lines[i][num_whitespace].isspace():
            endpoint = i
            break

    return "\n".join(lines[:endpoint])


def get_for_node(frame: types.FrameType) -> astroid.For:
    """Return the For node from the frame containing the accumulator loop"""
    func_string = inspect.cleandoc(inspect.getsource(frame))
    with_stmt_index = inspect.getlineno(frame) - frame.f_code.co_firstlineno
    lst_str_lines = func_string.splitlines()
    lst_from_with_stmt = lst_str_lines[with_stmt_index + 1 :]
    num_whitespace = num_whitespaces(lst_str_lines[with_stmt_index])
    loop_lines = get_loop_lines(lst_from_with_stmt, num_whitespace)

    return astroid.parse(loop_lines).body[0]


class AccumulationTable:
    """
    Class used as a form of print debugging to analyze different loop and
    accumulation variables during each iteration in a for loop

    Instance attributes:
        loop_accumulators: a mapping between the accumulation variables
            and their values during each iteration
        loop_variables: a mapping between the loop variables and their
            values during each iteration
        _loop_lineno: the line number of the for loop
    """

    loop_accumulators: dict[str, list]
    """A dictionary mapping loop accumulator variable name to its values across all loop iterations."""
    loop_variables: dict[str, list]
    """A dictionary mapping loop variable variable name to its values across all loop iterations."""
    _loop_lineno: int

    def __init__(self, accumulation_names: list[str]) -> None:
        """Initialize an Accumulation Table context manager for print-based loop debugging.

        Args:
            accumulation_names: a list of the loop accumulator variable names to display.

        """
        self.loop_accumulators = {accumulator: [] for accumulator in accumulation_names}
        self.loop_variables = {}
        self._loop_lineno = 0

    def _record_iteration(self, frame: types.FrameType) -> None:
        """Record the values of the accumulator variables and loop variables of an iteration"""
        if len(list(self.loop_variables.values())[0]) > 0:
            for loop_var in self.loop_variables:
                self.loop_variables[loop_var].append(copy.copy(frame.f_locals[loop_var]))
        else:
            for loop_var in self.loop_variables:
                self.loop_variables[loop_var].append("N/A")

        for accumulator in self.loop_accumulators:
            if accumulator in frame.f_locals:
                self.loop_accumulators[accumulator].append(copy.copy(frame.f_locals[accumulator]))
            else:
                raise NameError

    def _create_iteration_dict(self) -> dict:
        """Return a dictionary that maps each accumulator
        and loop variable to its respective value during each iteration
        """
        return {
            "iteration": list(range(len(list(self.loop_variables.values())[0]))),
            **self.loop_variables,
            **self.loop_accumulators,
        }

    def _tabulate_data(self) -> None:
        """Print the values of the accumulator and loop variables into a table"""
        iteration_dict = self._create_iteration_dict()
        print(
            tabulate.tabulate(
                iteration_dict,
                headers="keys",
                colalign=(*["left"] * len(iteration_dict),),
                disable_numparse=True,
                missingval="None",
            )
        )

    def _trace_loop(self, frame: types.FrameType, event: str, _arg: Any) -> None:
        """Trace through the for loop and store the values of the
        accumulators and loop variable during each iteration
        """
        if event == "line" and frame.f_lineno == self._loop_lineno:
            self._record_iteration(frame)

    def _setup_table(self) -> None:
        """
        Get the frame of the code containing the with statement, cut down the source code
        such that it only contains the with statement and the accumulator loop and set up
        the trace function to track the values of the accumulator variables during each iteration
        """
        func_frame = inspect.getouterframes(
            inspect.getouterframes(inspect.currentframe())[1].frame
        )[1].frame
        self._loop_lineno = inspect.getlineno(func_frame) + 1

        for_node = get_for_node(func_frame)
        if isinstance(for_node.target, astroid.Tuple):
            self.loop_variables = {loop_var.name: [] for loop_var in for_node.target.elts}
        else:
            self.loop_variables[for_node.target.name] = []

        func_frame.f_trace = self._trace_loop
        sys.settrace(lambda *_args: None)

    def __enter__(self) -> AccumulationTable:
        """Set up and return the accumulation table for the accumulator loop"""
        self._setup_table()
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        """Exit the accumulator loop, set the frame to none and print the table"""
        sys.settrace(None)
        inspect.getouterframes(inspect.currentframe())[1].frame.f_trace = None
        self._tabulate_data()
