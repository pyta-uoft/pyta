"""
Table data structure that prints a nicely formatted table
for a recursive function
"""
from __future__ import annotations

import inspect
import sys
import types
from typing import Any, Callable

import tabulate

from python_ta.util.tree import Tree


def clean_frame_variables(frame: types.FrameType) -> dict[str, Any]:
    """remove the local variables from the frame's locals and keep only the
    parameters
    """
    raw_variables = frame.f_locals
    parameters = inspect.getargvalues(frame).args
    # not mutating the local variables to avoid unintended effects
    cleaned_variables = {param: raw_variables[param] for param in parameters}
    return cleaned_variables


class RecursionTable:
    """
    Class used as a form of print debugging to analyze the inputs
    and return values for a recursive function

    Instance attributes:
        frames_mapping: a mapping between the frame for a
            recursive function and their return values and inputs
        frames_ordered: a list to conserve the order in which the
            frames were created
        function_name: name of the function being traced
        _trees: mapping of the frames to the corresponding tree
            representing the function call
    """

    frames_mapping: dict[types.FrameType, list]
    frames_ordered: list[types.FrameType]
    function_name: str
    _trees: dict[types.FrameType, Tree]

    def __init__(self) -> None:
        """Initialize a RecursionTable context manager for print-based recursive debugging."""
        self.frames_mapping = {}
        self.frames_ordered = []
        self._trees = {}
        self.function_name = ""

    def get_root(self) -> Tree:
        """To be used when we want to access the root node of the tree"""
        return self._trees[self.frames_ordered[0]]

    def _create_func_call_string(self, frame_variables: dict[str, Any]) -> str:
        """Create a string representation of the function call given the inputs
        for eg. fib(2, 3)
        """
        # note that in python dicts the order is maintained based on insertion
        # we don't need to worry about the order of inputs changing
        caller_val = f"{self.function_name}("
        count = 0
        for var in frame_variables:
            caller_val += f"{frame_variables[var]}"
            if count < len(frame_variables) - 1:
                caller_val += ", "
            count += 1
        caller_val += ")"
        return caller_val

    def _record_call(self, frame: types.FrameType) -> None:
        """Update the state of the table representation after a function call is detected"""
        self.frames_mapping[frame] = []
        self.frames_ordered.append(frame)
        caller_frame = frame.f_back
        caller_frame_variables = clean_frame_variables(caller_frame)

        # this handles the very first function call
        if not self.function_name:
            self.function_name = frame.f_code.co_name
            caller_func_string = "NA"
        else:
            caller_func_string = self._create_func_call_string(caller_frame_variables)
        self.frames_mapping[frame].append(caller_func_string)

        # tree insertion
        current_frame_variables = clean_frame_variables(frame)
        current_func_string = self._create_func_call_string(current_frame_variables)
        current_node = Tree([current_func_string])
        self._trees[frame] = current_node

        if caller_frame in self._trees:
            caller_node = self._trees[caller_frame]
            caller_node.add_child(current_node)

    def _record_return(self, frame: types.FrameType, return_value: Any) -> None:
        """Update the state of the table representation after a function return is detected
        Note: the frame must already have been seen as returns are done 'on the way out'
        """
        self.frames_mapping[frame].append(return_value)
        current_node = self._trees[frame]
        current_node.value.append(return_value)

    def get_recursive_dict(self) -> dict[str, list]:
        """Use the instance variables that define the table to create a final dictionary
        which directly represents the table
        """
        # intialize table columns
        parameters = inspect.getargvalues(self.frames_ordered[0]).args
        recursive_dict = {key: [] for key in parameters + ["called_by", "return_value"]}
        for frame in self.frames_ordered:
            current_frame_variables = clean_frame_variables(frame)
            for variable in current_frame_variables:
                recursive_dict[variable].append(current_frame_variables[variable])

            caller_expression, return_val = self.frames_mapping[frame]

            recursive_dict["called_by"].append(caller_expression)

            recursive_dict["return_value"].append(return_val)
        return recursive_dict

    def _tabulate_data(self) -> None:
        """Print the recursive table"""
        recursive_dict = self.get_recursive_dict()
        print(
            tabulate.tabulate(
                recursive_dict,
                headers="keys",
                colalign=(*["left"] * len(recursive_dict),),
                disable_numparse=True,
                missingval="None",
            )
        )

    def _trace_recursion(self, frame: types.FrameType, event: str, _arg: Any) -> Callable:
        """Trace through the recursive exexution and call the corresponding
        method depending on whether a call or return is detected
        """
        # ignore the execution of the __exit__ method
        if event == "call" and frame.f_code.co_name != "__exit__":
            self._record_call(frame)
        if event == "return":
            self._record_return(frame, _arg)

        # return the function to continue tracing
        return self._trace_recursion

    def __enter__(self) -> RecursionTable:
        """Set up and return the recursion table for the recursive function"""
        sys.settrace(self._trace_recursion)
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        """Exit the recursive execution, stop tracing function execution and print the table"""
        sys.settrace(None)
        self._tabulate_data()
