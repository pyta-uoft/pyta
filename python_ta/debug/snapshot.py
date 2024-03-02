"""
Use the 'inspect' module to extract local variables from
 multiple stack frames. Useful for dynamic debugging.
"""
import inspect
import json
from types import FrameType
from typing import Dict, List


def get_filtered_global_variables(frame: FrameType) -> Dict:
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


def snapshot_to_json(snapshot_data: List[Dict]):
    """
    Convert the snapshot data into a simplified JSON format, where each primitive value
    has its own entry with a matching ID.
    """
    json_data = []
    value_entries = []
    global_ids = {}
    id_counter = 1

    for frame in snapshot_data:
        frame_variables = {}
        for frame_name, frame_data in frame.items():
            for var_name, value in frame_data.items():
                var_id = id(value)
                if var_id not in global_ids:
                    global_ids[var_id] = id_counter
                    var_id_diagram = id_counter
                else:
                    var_id_diagram = global_ids[var_id]
                frame_variables[var_name] = var_id_diagram
                id_counter += 1
                # Create a separate entry for the variable's value
                value_entry = {
                    "isClass": False,
                    "name": type(value).__name__,
                    "id": global_ids[var_id],
                    "value": value,
                }
                value_entries.append(value_entry)

            # Create an entry for the stack frame
            json_object_frame = {
                "isClass": True,
                "name": frame_name,
                "id": None,
                "value": frame_variables,  # Reference the unique IDs for each variable
                "stack_frame": True,
            }
            json_data.append(json_object_frame)

    # Combine the stack frames and value entries
    json_data.extend(value_entries)
    final_json = json.dumps(json_data, indent=2)
    return final_json
