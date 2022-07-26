"""
Table data structure that prints a nicely formatted table
for an accumulator loop
"""
from __future__ import annotations

import inspect
import sys

import astroid
import tabulate


def no_of_whitespaces(with_line: str) -> int:
    """Return the number of whitespaces that are in the line of code
    containing the with statement
    """
    blank_chars = 0
    for char in with_line:
        if char == " ":
            blank_chars += 1
        else:
            break

    return blank_chars


def loop_string(full_string: list[str], no_whitespaces: int) -> str:
    """Convert the list of lines that are strings from the beginning of the for loop
    to the end of the for loop
    """
    endpoint = len(full_string)
    for i in range(len(full_string)):
        if full_string[i].strip() != "" and not full_string[i][no_whitespaces].isspace():
            endpoint = i
            break

    return "\n".join(full_string[:endpoint])


def setup_table(table: AccumulationTable) -> None:
    """
    Get the frame of the code containing the with statement, cut down the source code
    such that it only contains the with statement and the accumulator loop and set up
    the trace function to track the values of the accumulator variables during each iteration
    """
    class_frame = inspect.getouterframes(inspect.currentframe())[1].frame
    func_frame = inspect.getouterframes(class_frame)[1].frame
    func_string = inspect.cleandoc(inspect.getsource(func_frame))

    lst_str_lines = func_string.splitlines()
    with_stmt_index = inspect.getlineno(func_frame) - func_frame.f_code.co_firstlineno
    table.get_lineno(inspect.getlineno(func_frame) + 1)
    lst_from_with_stmt = lst_str_lines[with_stmt_index + 1 :]
    no_whitespaces = no_of_whitespaces(lst_str_lines[with_stmt_index])
    loop_str = loop_string(lst_from_with_stmt, no_whitespaces)

    func_node = astroid.parse(loop_str).body[0]
    table.add_zero_iter(func_node, func_frame)

    func_frame.f_trace = table.trace_loop
    sys.settrace(lambda *_args: None)


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
        _zero_iteration: a variable to keep track of and skip
            the zeroth iteration of the accumulator loop

    """

    loop_accumulators: dict[str, list]
    loop_var_name: str
    loop_var_val: list
    _loop_lineno: int
    _zero_iteration: bool

    def __init__(self, accumulation_names: list) -> None:
        self.loop_accumulators = {accumulator: [] for accumulator in accumulation_names}
        self.loop_var_name = ""
        self.loop_var_val = []
        self._loop_lineno = 0
        self._zero_iteration = True

    def get_lineno(self, line_no: int) -> None:
        """Get the line number of the for loop nested in the with statement"""
        self._loop_lineno = line_no

    def _add_iteration(self, val: list, var: Any) -> None:
        """Add the values of the accumulator and loop variables of an iteration"""
        self.loop_var_val.append(var)
        for index, key in enumerate(self.loop_accumulators):
            self.loop_accumulators[key].append(val[index])

    def _create_iteration_dict(self) -> dict:
        """Use the values of each iteration and return a dictionary that maps each accumulator
        and loop variable to its respective value during each iteration
        """
        return {
            "iteration": list(range(len(self.loop_accumulators[list(self.loop_accumulators)[0]]))),
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

    def add_zero_iter(self, func_node: types.NodeNG, func_frame: types.FrameType) -> None:
        """Add the names and values of the all the accumulators for the zeroth iteration"""
        self.loop_var_name = func_node.target.name
        for name in self.loop_accumulators:
            if name in func_frame.f_locals:
                self.loop_accumulators[name] = [func_frame.f_locals[name]]
            else:
                raise NameError

    def trace_loop(self, frame: types.FrameType, event: str, arg: Any) -> None:
        """Trace through the for loop and store the values of the
        accumulators during each iteration
        """
        if event == "line" and frame.f_lineno == self._loop_lineno:
            local_vars = frame.f_locals
            curr_vals = []
            for accumulator in self.loop_accumulators:
                if accumulator in local_vars:
                    curr_vals.append(local_vars[accumulator])
                else:
                    raise NameError

            if self.loop_var_name in local_vars and not self._zero_iteration:
                self._add_iteration(curr_vals, local_vars[self.loop_var_name])

            self._zero_iteration = False

    def __enter__(self) -> AccumulationTable:
        self.loop_var_val.append("N/A")
        setup_table(self)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        sys.settrace(None)
        inspect.getouterframes(inspect.currentframe())[1].frame.f_trace = None
        self._tabulate_data()
