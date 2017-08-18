"""Patch pylint checker behaviour.
"""
import astroid
from astroid.bases import BUILTINS
from pylint.utils import OPTION_RGX
from pylint.checkers.base import NameChecker
from pylint.checkers.classes import ClassChecker
from pylint.checkers.utils import node_frame_class
from pylint.checkers.format import FormatChecker, _EMPTY_LINE
from python_ta.checkers.global_variables_checker import is_in_main
from re import match, compile


def patch_checkers():
    """Run patches to modify built-in pylint checker behaviour."""
    _override_check_protected_attribute_access()
    _override_check_invalid_name_in_main()
    _override_attribute_defined_outside_init()
    _override_regex_to_allow_long_doctest_lines()


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
        if klass is None or (
                attrname not in klass.instance_attrs and
                attrname not in (m.name for m in klass.methods())):
            old_check_protected_attribute_access(self, node)

    ClassChecker._check_protected_attribute_access = _check


def _override_check_invalid_name_in_main():
    """Override invalid-name check for variables in main block.

    pylint normally complains about variable names in the main block
    that aren't in ALL_CAPS -- in other words, it assumes that all such
    variables should be constants. We disable this check here so that
    non-constant variable names are permitted (encourages experimentation
    in the main block).
    """
    old_visit_assignname = NameChecker.visit_assignname

    def patched_visit_assignname(self, node):
        if is_in_main(node):
            self._check_name('variable', node.name, node)
        else:
            old_visit_assignname(self, node)

    NameChecker.visit_assignname = patched_visit_assignname


def _override_attribute_defined_outside_init():
    """Eliminate attribute-defined-outside-init error when using properties.

    Checks for properties using the "a = property(_get_a, _set_a)" approach
    (no decorator support yet), and allows for a member to be set in the setter
    as long as the setter is called (implicitly) in __init__.
    """
    old_leave_classdef = ClassChecker.leave_classdef

    def new_leave_classdef(self, cnode):
        for attr, nodes in cnode.instance_attrs.items():
            setter = _get_attribute_property_setter(attr, cnode)
            if setter is not None:
                self.config.defining_attr_methods = self.config.defining_attr_methods + (setter, )

        old_leave_classdef(self, cnode)

    ClassChecker.leave_classdef = new_leave_classdef


def _get_attribute_property_setter(name, klass):
    """Return the name of a setter for name in klass, if name is a property."""
    try:
        attributes = klass.getattr(name)
    except astroid.NotFoundError:
        return None

    property_name = "{0}.property".format(BUILTINS)
    for attr in attributes:
        try:
            infered = next(attr.infer())
        except astroid.InferenceError:
            continue
        if infered.pytype() == property_name:
            try:
                # In this case, attr is in a statement of the form
                # <attr> = property(<fget>, <fset>); return the name of <fset>,
                # assuming it is an identifier (and not a more complex expression).
                return attr.parent.value.args[1].name
            except Exception:
                return None

def _override_regex_to_allow_long_doctest_lines():
    """Allow too-long lines for doctests.
    Mostly a copy from `pylint/checkers/format.py`
    Parts newly added are marked with comment, "[PYTA added]: ..."
    """

    def new_check_lines(self, lines, i):
        """check lines have less than a maximum number of characters
        """
        max_chars = self.config.max_line_length
        ignore_long_line = self.config.ignore_long_lines

        def check_line(line, i, prev_line=None):
            if not line.endswith('\n'):
                self.add_message('missing-final-newline', line=i)
            else:
                # exclude \f (formfeed) from the rstrip
                stripped_line = line.rstrip('\t\n\r\v ')
                if not stripped_line and _EMPTY_LINE in self.config.no_space_check:
                    # allow empty lines
                    pass
                elif line[len(stripped_line):] not in ('\n', '\r\n'):
                    self.add_message('trailing-whitespace', line=i)
                # Don't count excess whitespace in the line length.
                line = stripped_line
            mobj = OPTION_RGX.search(line)
            if mobj and mobj.group(1).split('=', 1)[0].strip() == 'disable':
                line = line.split('#')[0].rstrip()

            if len(line) > max_chars and not ignore_long_line.search(line):
                self.add_message('line-too-long', line=i, args=(len(line), max_chars))
            return i + 1

        unsplit_ends = {
            '\v', '\x0b', '\f', '\x0c', '\x1c', '\x1d', '\x1e', '\x85', '\u2028', '\u2029'}
        unsplit = []
        _split_lines = lines.splitlines(True)
        # [PYTA added]: enumerate to get line_i index.
        for line_i, line in enumerate(_split_lines):
            if line[-1] in unsplit_ends:
                unsplit.append(line)
                continue

            if unsplit:
                unsplit.append(line)
                line = ''.join(unsplit)
                unsplit = []

            # [PYTA added]: Skip error message for long doctest lines
            doctest_tokens = compile(r'^\s*>>>.*?\n$')
            if match(doctest_tokens, line):
                continue
            elif line_i > 0 and match(doctest_tokens, _split_lines[line_i-1]):
                continue

            i = check_line(line, i)

        if unsplit:
            check_line(''.join(unsplit), i)

    FormatChecker.check_lines = new_check_lines
