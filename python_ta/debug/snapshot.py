"""
Use the 'inspect' module to extract local variables from
 multiple stack frames. Useful for dynamic debugging.
"""
import inspect


def get_filtered_global_variables(frame) -> dict:
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
    local_vars = []
    frame = inspect.currentframe().f_back

    while frame:
        # whether the current stack frame corresponds to the global module context or not
        if frame.f_code.co_name != "<module>":  # skips the global module context
            local_vars.append({frame.f_code.co_name: frame.f_locals})

        global_vars = get_filtered_global_variables(frame)
        if global_vars not in local_vars:  # to avoid duplicates in nested function calls
            local_vars.append(global_vars)

        frame = frame.f_back

    return local_vars


# The functions (and top-level variables) below are for snapshot() testing purposes ONLY
team_lead = "David Liu"
SDS_projects = ["PyTA", "MarkUs", "Memory Models"]
team_num = 9


def func1() -> list:
    """
    Function for snapshot() testing.
    """
    test_var1a = "David is cool!"
    test_var2a = "Students Developing Software"
    return snapshot()


def func2() -> list:
    """
    Function for snapshot() testing.
    """
    test_var1b = {"SDS_coolest_project": "PyTA"}
    test_var2b = ("Aina", "Merrick", "Varun", "Utku")
    return func1()


if __name__ == "__main__":
    local_vars = func1()
    print(local_vars)
