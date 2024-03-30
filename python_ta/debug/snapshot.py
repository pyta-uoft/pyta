"""
Use the 'inspect' module to extract local variables from
 multiple stack frames. Useful for dynamic debugging.
"""

from __future__ import annotations

import inspect
from types import FrameType


def get_filtered_global_variables(frame: FrameType) -> dict:
    """
    Helper function for retriving global variables
    (i.e. top level variables in "__main__" frame's scope)
    excluding, certain types (types of data that is
    irrelevant in an intro level to Python programming language).
    """
    global_vars = frame.f_globals
    true_global_vars = {
        var: global_vars[var]
        for var in global_vars
        if not var.startswith("__")
        and not inspect.ismodule(global_vars[var])
        and not inspect.isfunction(global_vars[var])
        and not inspect.isclass(global_vars[var])
    }
    return {"__main__": true_global_vars}


def snapshot():
    """Capture a snapshot of local variables from the current and outer stack frames
    where the 'snapshot' function is called. Returns a list of dictionaries,
    each mapping function names to their respective local variables.
    Excludes the global module context.
    """
    variables = []
    frame = inspect.currentframe().f_back

    while frame:
        if frame.f_code.co_name != "<module>":
            variables.append({frame.f_code.co_name: frame.f_locals})
        else:
            global_vars = get_filtered_global_variables(frame)
            variables.append(global_vars)

        frame = frame.f_back

    return variables


def process_value(value, global_ids, value_entries, id_counter):
    """
    Recursively process a value, handling compound built-in data types
    (lists, sets, tuples, and dicts) by creating a list or dict of IDs for their elements.
    """
    value_id = id(value)
    if value_id not in global_ids:
        global_ids[value_id] = id_counter[0]
        value_id_diagram = id_counter[0]
        id_counter[0] += 1

        if isinstance(value, (list, set, tuple)):
            # For lists, sets, and tuples, process each element and store their IDs
            element_ids = [
                process_value(element, global_ids, value_entries, id_counter) for element in value
            ]

            # Create the value entry with a list of IDs for its elements
            value_entry = {
                "isClass": False,
                "name": type(value).__name__,
                "id": value_id_diagram,
                "value": element_ids,
            }
        elif isinstance(value, dict):
            # For dicts, process each key-value pair and store their IDs
            dict_ids = {}
            for key, val in value.items():
                key_id = process_value(key, global_ids, value_entries, id_counter)
                val_id = process_value(val, global_ids, value_entries, id_counter)
                dict_ids[key_id] = val_id  # Store the ID as an integer key

            # Create the value entry with a dictionary of IDs for its keys and values
            value_entry = {
                "isClass": False,
                "name": "dict",
                "id": value_id_diagram,
                "value": dict_ids,
            }
        else:
            # Primitive types are directly stored
            value_entry = {
                "isClass": False,
                "name": type(value).__name__,
                "id": value_id_diagram,
                "value": value,
            }

        value_entries.append(value_entry)
    else:
        value_id_diagram = global_ids[value_id]

    return value_id_diagram


def snapshot_to_json(snapshot_data):
    """
    Convert the snapshot data into a simplified JSON format, where each value
    has its own entry with a matching ID.
    """

    json_data = []
    value_entries = []
    global_ids = {}
    id_counter = [1]  # Using a list for a mutable integer reference

    for frame in snapshot_data:
        frame_variables = {}
        for frame_name, frame_data in frame.items():
            for var_name, value in frame_data.items():
                # Process each variable in the frame, handling compound and primitive types
                var_id_diagram = process_value(value, global_ids, value_entries, id_counter)
                frame_variables[var_name] = var_id_diagram

            # Add the frame itself as an entry
            json_object_frame = {
                "isClass": True,
                "name": frame_name,
                "id": None,
                "value": frame_variables,  # Map of variable names to their unique IDs
                "stack_frame": True,
            }
            json_data.append(json_object_frame)

    json_data.extend(value_entries)
    return json_data
