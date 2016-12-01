"""Patch pylint checker behaviour.
"""
from pylint.checkers.classes import ClassChecker
from pylint.checkers.utils import node_frame_class


def patch_checkers():
    """Run patches to modify built-in pylint checker behaviour."""
    _override_check_protected_attribute_access()


def _override_check_protected_attribute_access():
    """Override protected-member-access check.

    We find pylint's default protected-member-access check too restrictive in
    method bodies; it only allows protected attribute access on the 'self'
    parameter (and from the class itself).

    We change this behaviour to allow access to any protected attribute that is
    defined for this class. (This leads to false negatives unless we combine
    this with type inference, but we're okay with that.)
    """
    old_check_protected_attribute_access =\
        ClassChecker._check_protected_attribute_access

    def _check(self, node):
        attrname = node.attrname
        klass = node_frame_class(node)
        if klass is None or attrname not in klass.instance_attrs:
            old_check_protected_attribute_access(self, node)

    ClassChecker._check_protected_attribute_access = _check

