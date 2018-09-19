"""Patch pylint error messages."""
from pylint.checkers.base import PassChecker


def patch_error_messages():
    """Override pylint error messages."""
    patch_passchecker_msgs()


def patch_passchecker_msgs():
    """Override PassChecker msgs."""
    lst = list(PassChecker.msgs['W0107'])
    lst[0] += ' (you should remove this)'
    PassChecker.msgs['W0107'] = tuple(lst)

# TODO: patch more pylint error messages
