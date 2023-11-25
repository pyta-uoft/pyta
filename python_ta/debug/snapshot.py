"""
Use the 'inspect' module to extract local variables from
 multiple stack frames. Useful for dynamic debugging.
"""
import inspect


def snapshot():
    """Capture a snapshot of local variables from the current and outer stack frames
    where the 'snapshot' function is called. Returns a list of dictionaries,
    each mapping function names to their respective local variables.
    Excludes the global module context.
    """
    local_vars = []
    frame = inspect.currentframe().f_back

    while frame:
        if frame.f_code.co_name != "<module>":
            local_vars.append({frame.f_code.co_name: frame.f_locals})
        frame = frame.f_back

    return local_vars
