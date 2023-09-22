"""A checker used for identifying names that don't conform to Python naming conventions."""

import re
from typing import List, Optional

from astroid import nodes
from pylint.checkers import BaseChecker, utils
from pylint.checkers.base.name_checker.checker import _redefines_import
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter

# Bad variable names.
BAD_NAMES = {"l", "I", "O"}

# Set a limit in name length to keep certain variable names short.
VAR_NAME_LENGTHS = {
    "module": 30,
    "constant": 30,
    "class": 30,
    "function": 30,
    "method": 30,
    "attribute": 30,
    "argument": 30,
    "variable": 30,
    "class attribute": 30,
    "class constant": 30,
    "type variable": 20,
    "type alias": 20,
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
    pattern = "(_?[a-z][a-z0-9_]*)$"

    return re.match(pattern, name) is not None


def _is_in_pascal_case(name: str) -> bool:
    """Returns whether `name` is in PascalCase.

    `name` is in PascalCase if:
      - `name` starts with an uppercase letter or an underscore (to denote private fields) followed
        by an uppercase letter.
      - each word has its first character capitalized, and
      - there is no whitespace, underscore, or punctuation between words.
    """
    pattern = "(_?[A-Z][a-zA-Z0-9]*)$"

    return re.match(pattern, name) is not None


def _is_in_upper_case_with_underscores(name: str) -> bool:
    """Returns whether `name` is in UPPER_CASE_WITH_UNDERSCORES.

    `name` is in `UPPER_CASE_WITH_UNDERSCORES if:
      - each word is in uppercase, and
      - words are separated by an underscore.
    """
    pattern = "(_?[A-Z][A-Z0-9_]*)$"

    return re.match(pattern, name) is not None


def _is_bad_name(name: str) -> str:
    """Returns a string detailing why `name` is a bad name.

    `name` is a bad name if it is in the pre-determined collection of "bad names".

    Returns the empty string if `name` is not a bad name."""
    msg = ""

    if name in BAD_NAMES:
        msg = (
            f'"{name}" is a name that should be avoided. Change to something less ambiguous '
            f"and/or more descriptive."
        )

    return msg


def _is_within_name_length(node_type: str, name: str) -> str:
    """Returns a string saying that `name` exceeds the character limit for that variable name type.

    Returns the empty string if `name` is within the name length limit."""
    msg = ""
    name_length_limit = VAR_NAME_LENGTHS[node_type]

    if len(name) > name_length_limit:
        msg = (
            f'{node_type.capitalize()} name "{name}" exceeds the limit of {name_length_limit} '
            f"characters."
        )

    return msg


def _check_module_name(_node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates Python naming conventions for
    module names.

    Returns an empty list if `name` is a valid module name."""
    error_msgs = []

    if not _is_in_snake_case(name):
        error_msgs.append(
            f'Module name "{name}" should be in snake_case format. Modules should be all-lowercase '
            f"names, with each name separated by underscores."
        )

    return error_msgs


def _check_const_name(node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates Python naming conventions for
    constant and class constant names.

    Returns an empty list if `name` is a valid (global or class) constant name."""
    error_msgs = []

    if not _is_in_upper_case_with_underscores(name):
        msg = (
            f'{node_type.capitalize()} name "{name}" should be in UPPER_CASE_WITH_UNDERSCORES format. '
            f"Constants should be all-uppercase words with each word separated by an "
            f"underscore. A single leading underscore can be used to denote a private constant."
        )
        if node_type == "class constant":
            msg += " A double leading underscore invokes Python's name-mangling rules."
        error_msgs.append(msg)

    return error_msgs


def _check_class_name(_node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates Python naming conventions for
    class names.

    Returns an empty list if `name` is a valid class name."""
    error_msgs = []

    if not _is_in_pascal_case(name):
        error_msgs.append(
            f'Class name "{name}" should be in PascalCase format. Class names should have the '
            f"first letter of each word capitalized with no separation between each "
            f"word. A single leading underscore can be used to denote a private "
            f"class."
        )

    return error_msgs


def _check_function_and_variable_name(node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates Python naming conventions for
    function and variable names.

    Returns an empty list if `name` is a valid function or variable name."""
    error_msgs = []

    if name != "_" and not _is_in_snake_case(name):
        error_msgs.append(
            f'{node_type.capitalize()} name "{name}" should be in snake_case format. '
            f"{node_type.capitalize()} names should be lowercase, with words "
            f"separated by underscores. A single leading underscore can be used to "
            f"denote a private {node_type}."
        )

    return error_msgs


def _check_method_and_attr_name(node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates Python naming conventions for
    method and instance or class attribute names.

    Returns an empty list if `name` is a valid method, instance, or attribute name."""
    error_msgs = []

    # Also consider the case of invoking Python's name mangling rules with leading dunderscores.
    if not (_is_in_snake_case(name) or (name.startswith("__") and _is_in_snake_case(name[2:]))):
        error_msgs.append(
            f'{node_type.capitalize()} name "{name}" should be in snake_case format. '
            f"{node_type.capitalize()} names should be lowercase, with words "
            f"separated by underscores. A single leading underscore can be used to "
            f"denote a private {node_type} while a double leading underscore invokes "
            f"Python's name-mangling rules."
        )

    return error_msgs


def _check_argument_name(_node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates Python naming conventions for
    argument names.

    Returns an empty list if `name` is a valid argument name."""
    error_msgs = []

    if not _is_in_snake_case(name):
        error_msgs.append(
            f'Argument name "{name}" should be in snake_case format. Argument names should be '
            f"lowercase, with words separated by underscores. A single leading "
            f"underscore can be used to indicate that the argument is not being used "
            f"but is still needed somehow."
        )

    return error_msgs


def _check_typevar_name(_node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates Python naming conventions for
    type variable names.

    Returns an empty list if `name` is a valid type variable name."""
    error_msgs = []

    if not _is_in_pascal_case(name):
        error_msgs.append(
            f'Type variable name "{name}" should be in PascalCase format. Type variable '
            f"names should have the first letter of each word capitalized with no separation "
            f"between each word."
        )

    return error_msgs


def _check_type_alias_name(_node_type: str, name: str) -> List[str]:
    """Returns a list of strings, each detailing how `name` violates Python naming conventions for
    type alias names.

    Returns an empty list if `name` is a valid type alias name."""
    error_msgs = []

    if not _is_in_pascal_case(name):
        error_msgs.append(
            f'Type alias name "{name}" should be in PascalCase format. Type alias names should '
            f"have the first letter of each word capitalized with no separation "
            f"between each word."
        )

    return error_msgs


# Map each variable name type to its corresponding check
NAME_CHECK = {
    "module": _check_module_name,
    "constant": _check_const_name,
    "class": _check_class_name,
    "function": _check_function_and_variable_name,
    "method": _check_method_and_attr_name,
    "attribute": _check_method_and_attr_name,
    "argument": _check_argument_name,
    "variable": _check_function_and_variable_name,
    "class attribute": _check_method_and_attr_name,
    "class constant": _check_const_name,
    "type variable": _check_typevar_name,
    "type alias": _check_type_alias_name,
}


class InvalidNameChecker(BaseChecker):
    """A checker class to report on names that don't conform to Python naming conventions.

    For the Python naming conventions, see https://peps.python.org/pep-0008/#naming-conventions.
    """

    name = "naming_convention_violation"
    # Template of displayed message will include the following:
    #   1. Describe the variable name type (e.g. `module`, `const`, etc.) and the name itself.
    #   2. Explanation of how the name violates the naming convention and suggest a
    #   correction(s), if appropriate.
    msgs = {
        "C9103": (
            "%s",
            "naming-convention-violation",
            "Used when the name doesn't conform to standard Python naming conventions.",
        ),
        "C9104": (
            "%s",
            "module-name-violation",
            "Used when the name doesn't conform to standard Python naming conventions.",
        ),
    }

    # this is important so that your checker is executed before others
    priority = -1

    @only_required_for_messages("module-name-violation")
    def visit_module(self, node: nodes.Module) -> None:
        """Visit a Module node to check for any name violations.

        Snippets taken from pylint.checkers.base.name_checker.checker."""
        self._check_name("module", node.name.split(".")[-1], node)

    @only_required_for_messages("naming-convention-violation")
    def visit_classdef(self, node: nodes.ClassDef):
        """Visit a Class node to check for any name violations.

        Taken from pylint.checkers.base.name_checker.checker."""
        self._check_name("class", node.name, node)

    @only_required_for_messages("naming-convention-violation")
    def visit_functiondef(self, node: nodes.FunctionDef) -> None:
        """Visit a FunctionDef node to check for any name violations.

        Snippets taken from pylint.checkers.base.name_checker.checker."""
        if node.is_method():
            if utils.overrides_a_method(node.parent.frame(future=True), node.name):
                return

        self._check_name("method" if node.is_method() else "function", node.name, node)

    visit_asyncfunctiondef = visit_functiondef

    @only_required_for_messages("naming-convention-violation")
    def visit_assignname(self, node: nodes.AssignName):
        """Visit an AssignName node to check for any name violations.

        Taken from pylint.checkers.base.name_checker.checker."""
        frame = node.frame(future=True)
        assign_type = node.assign_type()

        # Check names defined in comprehensions
        if isinstance(assign_type, nodes.Comprehension):
            self._check_name("variable", node.name, node)

        # Check names defined as function arguments.
        elif isinstance(assign_type, nodes.Arguments):
            self._check_name("argument", node.name, node)

        # Check names defined in module scope
        elif isinstance(frame, nodes.Module):
            # Check names defined in Assign nodes
            if isinstance(assign_type, nodes.Assign):
                inferred_assign_type = utils.safe_infer(assign_type.value)

                # Check TypeVar's and TypeAliases assigned alone or in tuple assignment
                if isinstance(node.parent, nodes.Assign):
                    if self._assigns_typevar(assign_type.value):
                        self._check_name("type variable", assign_type.targets[0].name, node)
                        return
                    if self._assigns_typealias(assign_type.value):
                        self._check_name("type alias", assign_type.targets[0].name, node)
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
                            "type variable",
                            assign_type.targets[0].elts[node.parent.elts.index(node)].name,
                            node,
                        )
                        return
                    if self._assigns_typealias(assigner):
                        self._check_name(
                            "type alias",
                            assign_type.targets[0].elts[node.parent.elts.index(node)].name,
                            node,
                        )
                        return

                # Check classes (TypeVar's are classes so they need to be excluded first)
                elif isinstance(inferred_assign_type, nodes.ClassDef):
                    self._check_name("class", node.name, node)

                # Don't emit if the name redefines an import in an ImportError except handler.
                elif not _redefines_import(node):
                    self._check_name("constant", node.name, node)
                else:
                    self._check_name("variable", node.name, node)

            # Check names defined in AnnAssign nodes
            elif isinstance(assign_type, nodes.AnnAssign):
                if utils.is_assign_name_annotated_with(node, "Final"):
                    self._check_name("constant", node.name, node)
                elif self._assigns_typealias(assign_type.annotation):
                    self._check_name("type alias", node.name, node)

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
                        self._check_name("class constant", node.name, node)
                        break
                    elif utils.is_assign_name_annotated_with(node, "ClassVar"):
                        self._check_name("class attribute", node.name, node)
                        break
                    elif isinstance(node.parent, nodes.AnnAssign):
                        self._check_name("attribute", node.name, node)
                        break
                else:
                    self._check_name("class attribute", node.name, node)

    def _check_name(self, node_type: str, name: str, node: nodes.NodeNG) -> None:
        """Check for a name that violates Python naming conventions."""
        name_check = NAME_CHECK[node_type]
        error_msgs = name_check(node_type, name)

        bad_name_msg = _is_bad_name(name)
        if bad_name_msg:
            error_msgs.append(bad_name_msg)

        name_length_msg = _is_within_name_length(node_type, name)
        if name_length_msg:
            error_msgs.append(name_length_msg)

        msg_id = "naming-convention-violation" if node_type != "module" else "module-name-violation"
        line_no = 1 if node_type == "module" else None

        for msg in error_msgs:
            self.add_message(msgid=msg_id, node=node, args=msg, line=line_no)

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
