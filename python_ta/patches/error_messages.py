"""Patch pylint error messages."""
from importlib import import_module

# global
patch_data = {
    'pylint.checkers.base':
        {'PassChecker':
             {'W0107': 'Unnecessary pass statement (you should remove this)'}
         }
}


# We are assuming only the first elements of the tuple values in <msgs> are being patched.
def patch_error_messages():
    """Patch <msgs> in pylint checkers to make them more helpful for python_ta clients."""
    for file_name, file_data in patch_data.items():
        for checker_name, checker_data in file_data.items():
            # only access the specific variable being changed
            checker = getattr(import_module(file_name), checker_name)
            if hasattr(checker, 'msgs'):
                for error_id, new_msg in checker_data.items():
                    lst_msg = list(checker.msgs[error_id])
                    # first element of the tuple value changed
                    lst_msg[0] = new_msg
                    checker.msgs[error_id] = tuple(lst_msg)
            else:
                print('no msgs attribute!')


# TODO: patch more pylint error messages
