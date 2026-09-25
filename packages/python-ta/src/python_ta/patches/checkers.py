"""Patch pylint checker behaviour."""

from typing import Any, cast

from pylint.checkers.base import NameChecker
from pylint.checkers.classes import ClassChecker
from pylint.checkers.utils import node_frame_class

from python_ta.utils import _is_in_main


def patch_checkers() -> None:
    """Run patches to modify built-in pylint checker behaviour."""
    _override_check_protected_attribute_access()
    _override_check_invalid_name_in_main()


def _override_check_protected_attribute_access() -> None:
    """Override protected-member-access check.

    We find pylint's default protected-member-access check too restrictive in
    method bodies; it only allows protected attribute access on the 'self'
    parameter (and from the class itself).

    We change this behaviour to allow access to any protected attribute that is
    defined for this class. (This leads to false negatives unless we combine
    this with type inference, but we're okay with that.)
    """
    old_check_protected_attribute_access = ClassChecker._check_protected_attribute_access

    def _check(self, node) -> None:
        attrname = node.attrname
        klass = node_frame_class(node)
        if klass is None or (
            attrname not in klass.instance_attrs
            and attrname not in (m.name for m in klass.methods())
        ):
            old_check_protected_attribute_access(self, node)

    # cast to Any to avoid mypy error: "Cannot assign to a method"
    cast(Any, ClassChecker)._check_protected_attribute_access = _check


def _override_check_invalid_name_in_main() -> None:
    """Override invalid-name check for variables in main block.

    pylint normally complains about variable names in the main block
    that aren't in ALL_CAPS -- in other words, it assumes that all such
    variables should be constants. We disable this check here so that
    non-constant variable names are permitted (encourages experimentation
    in the main block).
    """
    old_visit_assignname = NameChecker.visit_assignname

    def patched_visit_assignname(self, node) -> None:
        if _is_in_main(node):
            self._check_name("variable", node.name, node)
        else:
            old_visit_assignname(self, node)

    cast(Any, NameChecker).visit_assignname = patched_visit_assignname
