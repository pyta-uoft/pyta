"""
Table data structure that prints a nicely formatted table
for a recursive function.
"""

from __future__ import annotations

import copy
import inspect
import sys
import types
from typing import Any, Callable, Optional

import tabulate

from python_ta.util.tree import Tree

DEFAULT_FUNCTION_STRING = "N/A"


def clean_frame_variables(frame: types.FrameType) -> dict[str, Any]:
    """Remove the local variables from the frame's locals and keep only the
    parameters.
    """
    raw_variables = frame.f_locals
    parameters = inspect.getargvalues(frame).args
    cleaned_variables = {param: copy.deepcopy(raw_variables[param]) for param in parameters}
    return cleaned_variables


class RecursionTable:
    """
    Class used as a form of print debugging to analyze the inputs
    and return values for a recursive function.

    Instance attributes:
        frames_data: a mapping between the frame for a
            recursive function and its traced values
        function_name: name of the function to be traced
        _trees: mapping of the frames to the corresponding tree
            representing the function call
    """

    frames_data: dict[types.FrameType, dict[str, Any]]
    function_name: str
    _trees: dict[types.FrameType, Tree]

    def __init__(self, function_name: str) -> None:
        """Initialize a RecursionTable context manager for print-based recursive debugging
        of <function_name>.
        """
        self.function_name = function_name
        self.frames_data = {}
        self._trees = {}

    def _get_root(self) -> Optional[Tree]:
        """Return the root node of the tree."""
        if self.frames_data:
            return self._trees[next(iter(self.frames_data))]

    def _create_func_call_string(self, frame_variables: dict[str, Any]) -> str:
        """Create a string representation of the function call given the inputs
        for eg. 'fib(2, 3)'.
        """
        # note that in python dicts the order is maintained based on insertion
        # we don't need to worry about the order of inputs changing
        function_inputs = ", ".join(str(frame_variables[var]) for var in frame_variables)
        return f"{self.function_name}({function_inputs})"

    def _insert_to_tree(
        self, current_func_string: str, frame: types.FrameType, caller_frame: types.FrameType
    ) -> None:
        """Create a new node for self._trees and add it as a child for its parent frame, if applicable."""
        current_node = Tree([current_func_string])
        self._trees[frame] = current_node
        # this will always be true unless frame is the initial function call frame
        if caller_frame in self._trees:
            caller_node = self._trees[caller_frame]
            caller_node.add_child(current_node)

    def _record_call(self, frame: types.FrameType) -> None:
        """Update the state of the table representation after a function call is detected."""
        current_frame_data = {}
        caller_frame = frame.f_back
        current_frame_variables = clean_frame_variables(frame)

        # add the inputs to the dict
        for variable in current_frame_variables:
            current_frame_data[variable] = current_frame_variables[variable]

        # add the parent function call string
        if caller_frame not in self.frames_data:
            current_frame_data["called by"] = DEFAULT_FUNCTION_STRING
        else:
            current_frame_data["called by"] = self.frames_data[caller_frame]["call string"]

        # add the function call string for the current frame
        current_func_string = self._create_func_call_string(current_frame_variables)
        current_frame_data["call string"] = current_func_string

        self.frames_data[frame] = current_frame_data
        self._insert_to_tree(current_func_string, frame, caller_frame)

    def _record_return(self, frame: types.FrameType, return_value: Any) -> None:
        """Update the state of the table representation after a function return is detected.
        Note: the frame must already have been seen as returns are done 'on the way out'.
        """
        self.frames_data[frame]["return value"] = copy.deepcopy(return_value)
        current_node = self._trees[frame]
        current_node.value.append(return_value)

    def get_recursive_dict(self) -> dict[str, list]:
        """Use the instance variables that define the table to create a final dictionary
        which directly represents the table.
        """
        if not self.frames_data:
            return {}
        # intialize table columns using the first frame
        parameters = inspect.getargvalues(next(iter(self.frames_data))).args
        recursive_dict = {key: [] for key in parameters + ["return value", "called by"]}

        for frame in self.frames_data:
            current_frame_data = self.frames_data[frame]
            for key in current_frame_data:
                # this should always be true unless key == "call string"
                if key in recursive_dict:
                    recursive_dict[key].append(current_frame_data[key])
        return recursive_dict

    def _tabulate_data(self) -> None:
        """Print the recursive table."""
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
        method depending on whether a call or return is detected.
        """
        # only trace frames that match the correct function name
        if frame.f_code.co_name == self.function_name:
            if event == "call":
                self._record_call(frame)
            elif event == "return":
                self._record_return(frame, _arg)

        # return the function to continue tracing
        return self._trace_recursion

    def __enter__(self) -> RecursionTable:
        """Set up and return the recursion table for the recursive function."""
        sys.settrace(self._trace_recursion)
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        """Exit the recursive execution, stop tracing function execution and print the table."""
        sys.settrace(None)
        self._tabulate_data()
