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


def get_loop_nodes(frame: types.FrameType) -> Generator[Union[astroid.For, astroid.While]]:
    """Generator function returns the For or While node(s) from the frame containing the accumulator loop(s)"""
    func_string = inspect.cleandoc(inspect.getsource(frame))
    with_stmt_index = inspect.getlineno(frame) - frame.f_code.co_firstlineno
    lst_str_lines = func_string.splitlines()
    lst_from_with_stmt = lst_str_lines[with_stmt_index + 1 :]
    num_whitespace = num_whitespaces(lst_str_lines[with_stmt_index])
    with_lines = get_with_lines(lst_from_with_stmt, num_whitespace)

    with_module = astroid.parse(with_lines)
    for statement in with_module.nodes_of_class((astroid.For, astroid.While)):
        if isinstance(statement, (astroid.For, astroid.While)):
            yield statement


class AccumulationTable:
    """
    Class used as a form of print debugging to analyze different loop and
    accumulation variables during each iteration in a for or while loop

    Instance attributes:
        loop_accumulators: a mapping between the accumulation variables
            and their values during each iteration
        loop_variables: a mapping between the loop variables and their
            values during each iteration
        _loop_lineno: the line number of the loop
        output_filepath: the filepath  where the table will be written if it is passed in, defaults to None
    """

    loop_accumulators: dict[str, list]
    """A dictionary mapping loop accumulator variable name to its values across all loop iterations."""
    loop_variables: dict[str, list]
    """A dictionary mapping loop variable variable name to its values across all loop iterations."""
    _loop_lineno: int
    output_filepath: Optional[str]
    output_format: str

    def __init__(
        self,
        accumulation_names: list[str],
        output: Union[None, str] = None,
        format: Literal["table", "csv"] = "table",
    ) -> None:
        """Initialize an AccumulationTable context manager for print-based loop debugging.

        Args:
            accumulation_names: a list of the loop accumulator variable names to display.

        """
        # Can be shared, persists across loops
        self.loop_accumulators = {accumulator: [] for accumulator in accumulation_names}

        # self._loops is a list of dictionaries or the form:
        # {
        #   "loop_variables": loop_variables,
        #   "loop_lineno": loop_lineno,
        #   "loop_accumulators": loop_accumulators,
        # }
        self._loops = []
        self.output_filepath = output
        self.output_format = format

    def _record_iteration(self, frame: types.FrameType, loop_index: int) -> None:
        """Record the values of the accumulator variables and loop variables of an iteration"""
        loop_variables = self._loops[loop_index]["loop_variables"]
        if (
            self._loops[loop_index]["loop_variables"] != {}
            and len(list(self._loops[loop_index]["loop_variables"].values())[0]) > 0
        ):
            for loop_var in self._loops[loop_index]["loop_variables"]:
                self._loops[loop_index]["loop_variables"][loop_var].append(
                    copy.deepcopy(frame.f_locals[loop_var])
                )
        else:
            for loop_var in self._loops[loop_index]["loop_variables"]:
                self._loops[loop_index]["loop_variables"][loop_var].append(NO_VALUE)

        for accumulator in self.loop_accumulators:
            if accumulator in frame.f_locals:
                value = copy.deepcopy(frame.f_locals[accumulator])
            elif accumulator in frame.f_code.co_varnames or accumulator in frame.f_code.co_names:
                value = NO_VALUE
            else:
                # name error wil be raised if accumulator cannot be found
                try:
                    value = eval(accumulator, frame.f_globals, frame.f_locals)
                except NameError as e:
                    if (
                        sys.version_info >= (3, 10)
                        and e.name in self._loops[loop_index]["loop_variables"]
                    ):
                        value = NO_VALUE
                    else:
                        raise
                else:
                    value = copy.deepcopy(value)

            self._loops[loop_index]["loop_accumulators"][accumulator].append(value)

    def _create_iteration_dict(self) -> Generator[dict]:
        """Function generates dictionaries that maps (for every loop) each accumulator
        and loop variable to its respective value during each iteration
        """
        iteration = None
        for i, loop in enumerate(self._loops):
            if loop["loop_variables"] != {}:
                iteration = list(range(len(list(loop["loop_variables"].values())[0])))
            elif self.loop_accumulators != {}:
                iteration = list(range(len(list(self.loop_accumulators.values())[0])))

            yield {
                "current loop": i,
                "iteration": iteration,
                **loop["loop_variables"],
                **loop["loop_accumulators"],
            }

    def _tabulate_data(self) -> None:
        """Print the values of the accumulator and loop variables into a table"""
        iteration_dict_lst = list(self._create_iteration_dict())

        if self.output_filepath is None:
            file_io = sys.stdout
        else:
            try:
                file_io = open(self.output_filepath, "a", newline="")
            except OSError as e:
                print(f"Error opening output file: {e}")
                return

        try:
            if self.output_format == "table":
                table = tabulate.tabulate(
                    iteration_dict_lst,
                    headers="keys",
                    colalign=(*["left"] * len(iteration_dict_lst[0]),),
                    disable_numparse=True,
                    missingval="None",
                )
                file_io.write(table)
                file_io.write("\n")
            else:
                csv_preformat = [
                    dict(zip(iteration_dict_lst[0].keys(), row))
                    for row in zip(*iteration_dict_lst[0].values())
                ]
                writer = csv.DictWriter(file_io, fieldnames=iteration_dict_lst[0].keys())
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
            for i, loop in enumerate(self._loops):
                if frame.f_lineno == loop["loop_lineno"]:
                    self._record_iteration(frame, i)
                    break  # Loop has been found, can safely break

    def _setup_table(self) -> None:
        """
        Get the frame of the code containing the with statement, cut down the source code
        such that it only contains the with statement and the accumulator loop and set up
        the trace function to track the values of the accumulator variables during each iteration
        """
        # Could be simplified to: func_frame = inspect.getouterframes(inspect.currentframe())[2].frame
        func_frame = inspect.getouterframes(
            inspect.getouterframes(inspect.currentframe())[1].frame
        )[1].frame

        # Instead of getting 1, we should get all loops!!!
        nodes = list(get_loop_nodes(func_frame))
        # node = get_loop_node(func_frame)

        # Repeat process for all every node in nodes
        for node in nodes:
            loop_lineno = inspect.getlineno(func_frame) + node.lineno
            loop_variables = {}

            if isinstance(node, astroid.For):
                loop_variables = {
                    nested_node.name: []
                    for nested_node in node.target.nodes_of_class(astroid.AssignName)
                }

            assert (
                self.loop_accumulators != {} or loop_variables != {}
            ), "The loop accumulator and loop variables cannot be both empty"

            self._loops.append(
                {
                    "loop_variables": loop_variables,
                    "loop_lineno": loop_lineno,
                    "loop_accumulators": {acc: [] for acc in self.loop_accumulators.keys()},
                }
            )

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
