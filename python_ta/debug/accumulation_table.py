"""
Table data structure that prints a nicely formatted table
for an accumulator loop
"""
from __future__ import annotations

import inspect
import sys

import astroid
import tabulate


def num_whitespaces(start_of_loop: str) -> int:
    """Number of spaces at the beginning of the accumulation loop"""
    blank_chars = 0
    for char in start_of_loop:
        if char.isspace():
            blank_chars += 1
        else:
            break

    return blank_chars


def get_loop_lines(lines: list[str], num_whitespace: int) -> str:
    """Function that returns the lines from the start to the end
    of the accumulator loop
    """
    endpoint = len(lines)
    for i in range(len(lines)):
        if lines[i].strip() != "" and not lines[i][num_whitespace].isspace():
            endpoint = i
            break

    return "\n".join(lines[:endpoint])


def get_for_node(frame: types.FrameType) -> types.NodeNG:
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

    Private instance attributes:
        loop_accumulators: a mapping between the accumulation variables
            and their values during each iteration
        loop_var_name: the name of the loop variable
        loop_var_val: the values of the loop variable during each iteration
        _loop_lineno: the line number of the for loop

    """

    loop_accumulators: dict[str, list]
    loop_var_name: str
    loop_var_val: list
    _loop_lineno: int

    def __init__(self, accumulation_names: list) -> None:
        self.loop_accumulators = {accumulator: [] for accumulator in accumulation_names}
        self.loop_var_name = ""
        self.loop_var_val = []
        self._loop_lineno = 0
        self._zero_iteration = True

    def _record_iteration(
        self, accumulator_values: list, loop_variable_value: Any, frame: types.FrameType
    ) -> None:
        """Record the values of the accumulator variables and loop variable of an iteration"""
        if len(self.loop_var_val) > 0:
            self.loop_var_val.append(loop_variable_value)
            for index, accumulator in enumerate(self.loop_accumulators):
                self.loop_accumulators[accumulator].append(accumulator_values[index])
        else:
            # zeroth iteration
            self.loop_var_val.append("N/A")
            for name in self.loop_accumulators:
                if name in frame.f_locals:
                    self.loop_accumulators[name] = [frame.f_locals[name]]
                else:
                    raise NameError

    def _create_iteration_dict(self) -> dict:
        """Return a dictionary that maps each accumulator
        and loop variable to its respective value during each iteration
        """
        return {
            "iteration": list(range(len(self.loop_var_val))),
            "loop variable (" + self.loop_var_name + ")": self.loop_var_val,
            **self.loop_accumulators,
        }

    def _tabulate_data(self) -> None:
        """Print the values of the accumulator and loop variables into a table"""
        iteration_dict = self._create_iteration_dict()
        print(
            tabulate.tabulate(
                iteration_dict, headers="keys", colalign=(*["left"] * len(iteration_dict),)
            )
        )

    def trace_loop(self, frame: types.FrameType, event: str, arg: Any) -> None:
        """Trace through the for loop and store the values of the
        accumulators and loop variable during each iteration
        """
        if event == "line" and frame.f_lineno == self._loop_lineno:
            local_vars = frame.f_locals
            curr_vals = []
            for accumulator in self.loop_accumulators:
                if accumulator in local_vars:
                    curr_vals.append(local_vars[accumulator])
                else:
                    raise NameError

            if self.loop_var_name in local_vars and len(self.loop_var_val) > 0:
                self._record_iteration(curr_vals, local_vars[self.loop_var_name], None)

    def setup_table(self) -> None:
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
        self.loop_var_name = for_node.target.name
        self._record_iteration([], None, func_frame)

        func_frame.f_trace = self.trace_loop
        sys.settrace(lambda *_args: None)

    def __enter__(self) -> AccumulationTable:
        """Set up and return the accumulation table"""
        self.setup_table()
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        """Exit the accumulator loop, set the frame to none and print the table"""
        sys.settrace(None)
        inspect.getouterframes(inspect.currentframe())[1].frame.f_trace = None
        self._tabulate_data()
