from __future__ import annotations

import inspect

import astroid
import tabulate


class AccumulationTable:
    """
    Class used as a form of print debugging to analyze different loop and
    accumulation variables during each iteration in a for loop

    Private instance attributes:
        _num_iterations: the number of for loop iterations
        _accumulation_names: the variable names of the different accumulation variables
        _loop_accumulation_values: a mapping between the accumulation variables and their value during each iteration
        _loop_var_name: the name of the loop variable
        _loop_var_val: the value of the loop variable during each iteration

    """

    _num_iterations: int
    _accumulation_names: list[str]
    _loop_accumulation_values: dict[str, list]
    _loop_var_name: str
    _loop_var_val: list

    def __init__(self, accumulation_names: list) -> None:
        self._num_iterations = 0
        self._accumulation_names = accumulation_names
        self._loop_accumulation_values = {}
        self._loop_var_name = ""
        self._loop_var_val = []

    def add_iteration(self, val: list, var) -> None:
        """Add the values of the accumulator and loop variables of an iteration"""
        self._loop_var_val.append(var)
        for i in range(len(self._accumulation_names)):
            self._loop_accumulation_values[self._accumulation_names[i]].append(val[i])
        self._num_iterations += 1

    def _create_iteration_dict(self) -> dict:
        """Use the values of each iteration and return a dictionary that maps each accumulator
        and loop variable to its respective value during each iteration
        """
        table_dict = {
            "iterations": list(range(self._num_iterations + 1)),
            "loop variable (" + self._loop_var_name + ")": self._loop_var_val,
            **self._loop_accumulation_values,
        }
        return table_dict

    def _tabulate_data(self) -> None:
        """Print the values of the accumulator and loop variables into a table"""
        print(
            tabulate.tabulate(
                self._create_iteration_dict(), headers="keys", colalign=("left", "left", "left")
            )
        )

    def _no_of_whitespaces(self, with_line: str) -> int:
        """Return the number of indents that are in the line of code containing the with statement"""
        blank_chars = 0
        for char in with_line:
            if char == " ":
                blank_chars += 1
            else:
                break

        return blank_chars

    def _loop_string(self, full_string: list[str], no_whitespaces: int) -> str:
        """Convert the list of lines that are strings from the beginning of the for loop
        to the end of the for loop"""
        endpoint = len(full_string)
        for i in range(len(full_string)):
            if full_string[i] != "" and full_string[i][no_whitespaces] != " ":
                endpoint = i
                break

        return "\n".join(full_string[:endpoint])

    def _add_keys(self, func_node: types.NodeNG, func_frame: types.FrameType) -> None:
        """Add the names and values of the all the accumulators for the zeroth iteration"""
        self._loop_var_name = func_node.target.name
        for name in self._accumulation_names:
            if name in func_frame.f_locals:
                self._loop_accumulation_values[name] = [func_frame.f_locals[name]]
            else:
                raise NameError

    def __enter__(self) -> AccumulationTable:
        self._loop_var_val.append("N/A")
        func_frame = inspect.getouterframes(inspect.currentframe())[1].frame
        func_string = inspect.cleandoc(inspect.getsource(func_frame))
        lst_str_lines = func_string.splitlines()
        with_stmt_index = inspect.getlineno(func_frame) - func_frame.f_code.co_firstlineno

        lst_from_with_stmt = lst_str_lines[with_stmt_index + 1 :]
        no_whitespaces = self._no_of_whitespaces(lst_str_lines[with_stmt_index])
        loop_str = self._loop_string(lst_from_with_stmt, no_whitespaces)

        func_node = astroid.parse(loop_str).body[0]
        self._add_keys(func_node, func_frame)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        self._tabulate_data()
