"""A checker used for identifying names that don't conform to Python naming conventions."""

import re
from typing import List, Optional

from astroid import nodes
from pylint.checkers import BaseChecker, utils
from pylint.checkers.base.name_checker.checker import (
    _determine_function_name_type,
    _redefines_import,
)
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter

# Bad variable names.
BAD_NAMES = {"l", "I", "O"}

# Set a limit in name length to keep certain variable names short.
VAR_NAME_LENGTHS = {
    "module": 20,
    "typevar": 20,
}

TYPE_VAR_QNAME = frozenset(
    (
        "typing.TypeVar",
        "typing_extensions.TypeVar",
    )
)


def _is_in_snake_case(name: str) -> bool:
    """Returns whether `name` is in snake_case.

    `name` is in snake_case if:
      - `name` starts with a lowercase letter or an underscore (to denote private fields) followed
        by a lowercase letter,
      - each word is separated by an underscore, and
      - each word is in lowercase.
    """
    pattern = "(([a-z][a-z0-9_]{0,30})|(_[a-z][a-z0-9_]*))$"
    is_snake_case = False

    if re.match(pattern, name):
        is_snake_case = True

    return is_snake_case


def _is_in_pascal_case(name: str) -> bool:
    """Returns whether `name` is in PascalCase.

    `name` is in PascalCase if:
      - `name` starts with an uppercase letter or an underscore (to denote private fields) followed
        by an uppercase letter.
      - each word has its first character capitalized, and
      - there is no whitespace, underscore, or punctuation between words.
    """
    pattern = "(([A-Z][a-zA-Z0-9]{0,30})|(_[A-Z][a-zA-Z0-9]*))$"
    is_pascal_case = False

    if re.match(pattern, name):
        is_pascal_case = True

    return is_pascal_case


def _is_in_upper_case_with_underscores(name: str) -> bool:
    """Returns whether `name` is in UPPER_CASE_WITH_UNDERSCORES.

    `name` is in `UPPER_CASE_WITH_UNDERSCORES if:
      - each word is in uppercase, and
      - words are separated by an underscore.
    """
    pattern = "([A-Z_][A-Z0-9_]*)$"
    is_upper_case_with_underscores = False

    if re.match(pattern, name):
        is_upper_case_with_underscores = True

    return is_upper_case_with_underscores


def _is_bad_name(name: str) -> str:
    """Returns a string detailing why `name` is a bad name.

    `name` is a bad name if it is in the pre-determined collection of "bad names".

    Returns the empty string if `name` is not a bad name."""
    msg = ""

    # For bad single character names.
    if len(name) == 1 and name in BAD_NAMES:
        msg = (
            f'"{name}" is a single character name that should be avoided. In some fonts, these '
            f"characters are indistinguishable from the numbers 1 and 0."
        )

    return msg


def _check_module_name(_node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates the PEP8 naming conventions for
    module names.

    Returns an empty list if `name` is a valid module name."""
    error_msgs = []

    bad_name_msg = _is_bad_name(name)
    if bad_name_msg:
        error_msgs.append(bad_name_msg)

    name_length = VAR_NAME_LENGTHS["module"]
    if len(name) > name_length:
        error_msgs.append(
            f'Module name "{name}" is too long. Try to keep it short, i.e. below '
            f"{name_length} characters."
        )

    if not _is_in_snake_case(name):
        error_msgs.append(
            f'Module name "{name}" is not in snake_case. Modules should be '
            f"all-lowercase names, each possibly separated by underscores."
        )

    return error_msgs


def _check_const_name(node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates the PEP8 naming conventions for
    constant and class constant names.

    Returns an empty list if `name` is a valid (global or class) constant name."""
    error_msgs = []

    if not _is_in_upper_case_with_underscores(name):
        msg = (
            f'{node_type.capitalize()} name "{name}" is not in UPPER_CASE_WITH_UNDERSCORES. '
            f"Constants should be all-uppercase words with each word separated by an "
            f"underscore. A single leading underscore can be used to denote a private constant."
        )
        if node_type == "class_const":
            msg += " A double leading underscore invokes Python's name-mangling rules."
        error_msgs.append(msg)

    return error_msgs


def _check_class_name(_node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates the PEP8 naming conventions for
    class names.

    Returns an empty list if `name` is a valid class name."""
    error_msgs = []

    if not _is_in_pascal_case(name):
        error_msgs.append(
            f'Class name "{name}" is not in PascalCase. Class names should have the '
            f"first letter of each word capitalized with no separation between each "
            f"word. A single leading underscore can be used to denote a private "
            f"class."
        )

    return error_msgs


def _check_function_and_variable_name(node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates the PEP8 naming conventions for
    function and variable names.

    Returns an empty list if `name` is a valid function or variable name."""
    error_msgs = []

    bad_name_msg = _is_bad_name(name)
    if bad_name_msg:
        error_msgs.append(bad_name_msg)

    if not _is_in_snake_case(name):
        error_msgs.append(
            f'{node_type.capitalize()} name "{name}" is not in snake_case. '
            f"{node_type.capitalize()} names should be lowercase, with words "
            f"separated by underscores. A single leading underscore can be used to "
            f"denote a private {node_type}."
        )

    return error_msgs


def _check_method_and_attr_name(node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates the PEP8 naming conventions for
    method and instance or class attribute names.

    Returns an empty list if `name` is a valid method, instance, or attribute name."""
    error_msgs = []

    bad_name_msg = _is_bad_name(name)
    if bad_name_msg:
        error_msgs.append(bad_name_msg)

    # Also consider the case of invoking Python's name mangling rules with leading dunderscores.
    if not (_is_in_snake_case(name) or (name.startswith("__") and _is_in_snake_case(name[2:]))):
        error_msgs.append(
            f'{node_type.capitalize()} name "{name}" is not in snake_case. '
            f"{node_type.capitalize()} names should be lowercase, with words "
            f"separated by underscores. A single leading underscore can be used to "
            f"denote a private {node_type} while a double leading underscore invokes "
            f"Python's name-mangling rules."
        )

    return error_msgs


def _check_argument_name(_node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates the PEP8 naming conventions for
    argument names.

    Returns an empty list if `name` is a valid argument name."""
    error_msgs = []

    bad_name_msg = _is_bad_name(name)
    if bad_name_msg:
        error_msgs.append(bad_name_msg)

    if not _is_in_snake_case(name):
        error_msgs.append(
            f'Argument name "{name}" is not in snake_case. Argument names should be '
            f"lowercase, with words separated by underscores. A single leading "
            f"underscore can be used to indicate that the argument is not being used "
            f"but is still needed somehow."
        )

    return error_msgs


def _check_inlinevar_name(_node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates the PEP8 naming conventions for
    inline variable names.

    Returns an empty list if `name` is a valid inline variable name."""
    error_msgs = []

    bad_name_msg = _is_bad_name(name)
    if bad_name_msg:
        error_msgs.append(bad_name_msg)

    if not _is_in_snake_case(name):
        error_msgs.append(
            f'Inline variable name "{name}" is not in snake_case. Inline variable '
            f"names should be lowercase, with words separated by underscores. A "
            f'single underscore can be used to denote a "throwaway"/unused variable.'
        )

    return error_msgs


def _check_typevar_name(_node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates the PEP8 naming conventions for
    type variable names.

    Returns an empty list if `name` is a valid type variable name."""
    error_msgs = []
    pattern = "^_{0,2}[A-SU-Z]([A-Z]{0,20}|[a-zA-Z0-9]{0,20})T?(?<!Type)(?:_co(?:ntra)?)?$"

    bad_name_msg = _is_bad_name(name)
    if bad_name_msg:
        error_msgs.append(bad_name_msg)

    name_length = VAR_NAME_LENGTHS["typevar"]
    if len(name) > name_length:
        error_msgs.append(
            f'Typevar name "{name}" is too long. Try to keep it short, i.e. below '
            f"{name_length} characters."
        )

    if not re.match(pattern, name):
        error_msgs.append(
            f'Typevar name "{name}" does not abide by the naming convention. Typevar '
            f"names may start with 0-2 underscores, does not start with a capital T, "
            f"and is either in all capital letters and no underscores, or in "
            f'PascalCase, optionally ending in T and not ending with "Type", an '
            f'optional "_co" or "_contra" ending.'
        )

    return error_msgs


def _check_typealias_name(_node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates the PEP8 naming conventions for
    type alias names.

    Returns an empty list if `name` is a valid type alias name."""
    error_msgs = []

    bad_name_msg = _is_bad_name(name)
    if bad_name_msg:
        error_msgs.append(bad_name_msg)

    if not _is_in_pascal_case(name):
        error_msgs.append(
            f'Typealias name "{name}" is not in PascalCase. Typealias names should '
            f"have the first letter of each word capitalized with no separation "
            f"between each word."
        )

    return error_msgs


# Map each variable name type to its corresponding check
NAME_CHECK = {
    "module": _check_module_name,
    "const": _check_const_name,
    "class": _check_class_name,
    "function": _check_function_and_variable_name,
    "method": _check_method_and_attr_name,
    "attr": _check_method_and_attr_name,
    "argument": _check_argument_name,
    "variable": _check_function_and_variable_name,
    "class_attribute": _check_method_and_attr_name,
    "class_const": _check_const_name,
    "inlinevar": _check_inlinevar_name,
    "typevar": _check_typevar_name,
    "typealias": _check_typealias_name,
}


class InvalidNameChecker(BaseChecker):
    """A checker class to report on names that don't conform to PEP8 naming conventions.

    For the PEP8 naming conventions, see https://peps.python.org/pep-0008/#naming-conventions.
    """

    name = "pep8_name_violation"
    # Template of displayed message will include the following:
    #   1. Describe the variable name type (e.g. `module`, `const`, etc.) and the name itself.
    #   2. Explanation of how the name violates the naming convention and suggest a
    #   correction(s), if appropriate.
    msgs = {
        "C9103": (
            'Found %s name "%s" in violation of PEP8 naming conventions. %s',
            "pep8-name-violation",
            "Used when the name doesn't conform to naming conventions specified "
            "in the PEP8 style guide.",
        ),
    }

    # this is important so that your checker is executed before others
    priority = -1

    @only_required_for_messages("pep8-name-violation")
    def visit_module(self, node: nodes.Module) -> None:
        """Visit a Module node to check for any name violations.

        Snippets taken from pylint.checkers.base.name_checker.checker."""
        self._check_name("module", node.name.split(".")[-1], node)

    @only_required_for_messages("pep8-name-violation")
    def visit_classdef(self, node: nodes.ClassDef):
        """Visit a Class node to check for any name violations.

        Taken from pylint.checkers.base.name_checker.checker."""
        self._check_name("class", node.name, node)
        # Check any instance attributes that were first defined in this class.
        for attr, anodes in node.instance_attrs.items():
            if not any(node.instance_attr_ancestors(attr)):
                self._check_name("attr", attr, anodes[0])

    @only_required_for_messages("pep8-name-violation")
    def visit_functiondef(self, node: nodes.FunctionDef) -> None:
        """Visit a FunctionDef node to check for any name violations.

        Snippets taken from pylint.checkers.base.name_checker.checker."""
        if node.is_method():
            if utils.overrides_a_method(node.parent.frame(future=True), node.name):
                return

        self._check_name(
            _determine_function_name_type(node, config=self.linter.config), node.name, node
        )
        # Check argument names
        args = node.args.args
        if args is not None:
            self._recursive_check_names(args)

    visit_asyncfunctiondef = visit_functiondef

    @only_required_for_messages("pep8-name-violation")
    def visit_assignname(self, node: nodes.AssignName):
        """Visit an AssignName node to check for any name violations.

        Taken from pylint.checkers.base.name_checker.checker."""
        frame = node.frame(future=True)
        assign_type = node.assign_type()

        # Check names defined in comprehensions
        if isinstance(assign_type, nodes.Comprehension):
            self._check_name("inlinevar", node.name, node)

        # Check names defined in module scope
        elif isinstance(frame, nodes.Module):
            # Check names defined in Assign nodes
            if isinstance(assign_type, nodes.Assign):
                inferred_assign_type = utils.safe_infer(assign_type.value)

                # Check TypeVar's and TypeAliases assigned alone or in tuple assignment
                if isinstance(node.parent, nodes.Assign):
                    if self._assigns_typevar(assign_type.value):
                        self._check_name("typevar", assign_type.targets[0].name, node)
                        return
                    if self._assigns_typealias(assign_type.value):
                        self._check_name("typealias", assign_type.targets[0].name, node)
                        return

                if (
                    isinstance(node.parent, nodes.Tuple)
                    and isinstance(assign_type.value, nodes.Tuple)
                    # protect against unbalanced tuple unpacking
                    and node.parent.elts.index(node) < len(assign_type.value.elts)
                ):
                    assigner = assign_type.value.elts[node.parent.elts.index(node)]
                    if self._assigns_typevar(assigner):
                        self._check_name(
                            "typevar",
                            assign_type.targets[0].elts[node.parent.elts.index(node)].name,
                            node,
                        )
                        return
                    if self._assigns_typealias(assigner):
                        self._check_name(
                            "typealias",
                            assign_type.targets[0].elts[node.parent.elts.index(node)].name,
                            node,
                        )
                        return

                # Check classes (TypeVar's are classes so they need to be excluded first)
                elif isinstance(inferred_assign_type, nodes.ClassDef):
                    self._check_name("class", node.name, node)

                # Don't emit if the name redefines an import in an ImportError except handler.
                elif not _redefines_import(node) and isinstance(inferred_assign_type, nodes.Const):
                    self._check_name("const", node.name, node)
                else:
                    self._check_name("variable", node.name, node)

            # Check names defined in AnnAssign nodes
            elif isinstance(assign_type, nodes.AnnAssign):
                if utils.is_assign_name_annotated_with(node, "Final"):
                    self._check_name("const", node.name, node)
                elif self._assigns_typealias(assign_type.annotation):
                    self._check_name("typealias", node.name, node)

        # Check names defined in function scopes
        elif isinstance(frame, nodes.FunctionDef):
            # global introduced variable aren't in the function locals
            if node.name in frame and node.name not in frame.argnames():
                if not _redefines_import(node):
                    self._check_name("variable", node.name, node)

        # Check names defined in class scopes
        elif isinstance(frame, nodes.ClassDef):
            if not list(frame.local_attr_ancestors(node.name)):
                for ancestor in frame.ancestors():
                    if utils.is_enum(ancestor) or utils.is_assign_name_annotated_with(
                        node, "Final"
                    ):
                        self._check_name("class_const", node.name, node)
                        break
                else:
                    self._check_name("class_attribute", node.name, node)

    def _check_name(self, node_type: str, name: str, node: nodes.NodeNG) -> None:
        """Check for a name that violates the PEP8 naming conventions."""
        name_check = NAME_CHECK[node_type]
        # Update node_type to be more readable
        temp = node_type.split("_")
        node_type = " ".join(temp)
        error_msgs = name_check(node_type, name)

        for msg in error_msgs:
            args = (node_type, name, msg)
            self.add_message("pep8-name-violation", node=node, args=args)

    def _recursive_check_names(self, args: List[nodes.AssignName]) -> None:
        """Check names in a possibly recursive list <arg>.

        Taken from pylint.checkers.base.name_checker.checker.

        Preconditions:
          - args is not None
        """
        for arg in args:
            self._check_name("argument", arg.name, arg)

    @staticmethod
    def _assigns_typevar(node: Optional[nodes.NodeNG]) -> bool:
        """Check if a node is assigning a TypeVar.

        Taken from pylint.checkers.base.name_checker.checker."""
        if isinstance(node, nodes.Call):
            inferred = utils.safe_infer(node.func)
            if isinstance(inferred, nodes.ClassDef) and inferred.qname() in TYPE_VAR_QNAME:
                return True
        return False

    @staticmethod
    def _assigns_typealias(node: Optional[nodes.NodeNG]) -> bool:
        """Check if a node is assigning a TypeAlias.

        Taken from pylint.checkers.base.name_checker.checker."""
        inferred = utils.safe_infer(node)
        if isinstance(inferred, nodes.ClassDef):
            if inferred.qname() == ".Union":
                # Union is a special case because it can be used as a type alias
                # or as a type annotation. We only want to check the former.
                assert node is not None
                return not isinstance(node.parent, nodes.AnnAssign)
        elif isinstance(inferred, nodes.FunctionDef):
            if inferred.qname() == "typing.TypeAlias":
                return True
        return False


def register(linter: PyLinter) -> None:
    """Register this checker to the linter."""
    linter.register_checker(InvalidNameChecker(linter))
