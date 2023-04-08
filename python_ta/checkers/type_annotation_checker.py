"""checker for type annotation.
"""

from astroid import Uninferable, nodes
from astroid.exceptions import NoDefault
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages


class TypeAnnotationChecker(BaseChecker):
    name = "TypeAnnotationChecker"
    msgs = {
        "E9970": (
            "Function parameter is missing type annotation",
            "missing-param-type",
            "Presented when a type annotation is missing.",
        ),
        "E9971": (
            "Function is missing return type annotation",
            "missing-return-type",
            "Presented when a type annotation is missing.",
        ),
        "E9972": (
            "Attribute is missing type annotation in class body",
            "missing-attribute-type",
            "Presented when a type annotation is missing.",
        ),
        "E9995": (
            "Type is assigned instead of annotated.",
            "type-is-assigned",
            "Presented when a type is assigned instead of annotated.",
        ),
    }

    # this is important so that your checker is executed before others
    priority = -1

    def is_type(self, node):
        """Check if nodes such as <Name.int ...> represent builtin types."""
        inferred = node.inferred()
        if len(inferred) > 0 and inferred[0] is not Uninferable:
            if isinstance(inferred[0], nodes.ClassDef):
                return True
        return False

    @only_required_for_messages("missing-param-type", "missing-return-type", "type-is-assigned")
    def visit_functiondef(self, node):
        arguments = node.args.args
        names = [argument.name for argument in arguments]
        annotations = node.args.annotations
        for i in range(len(annotations)):
            if annotations[i] is None:
                # Check if function is a non-static instance method
                if (
                    i != 0
                    or not isinstance(node.parent, nodes.ClassDef)
                    or node.type == "staticmethod"
                ):
                    self.add_message("missing-param-type", node=arguments[i])
                    try:
                        default_value = node.args.default_value(names[i])
                    except NoDefault:
                        default_value = None
                    if default_value is not None:
                        if self.is_type(default_value):
                            self.add_message("type-is-assigned", node=arguments[i])
        if node.returns is None:
            self.add_message("missing-return-type", node=node.args)

    @only_required_for_messages("missing-attribute-type", "type-is-assigned")
    def visit_classdef(self, node):
        for attr_key in node.instance_attrs:
            attr_node = node.instance_attrs[attr_key][0]
            if isinstance(attr_node, nodes.AssignAttr):
                if attr_key not in node.locals and all(
                    attr_key not in base.locals for base in node.ancestors()
                ):
                    self.add_message("missing-attribute-type", node=attr_node)
                elif isinstance(attr_node.parent, nodes.AnnAssign):
                    self.add_message("missing-attribute-type", node=attr_node)

        for attr_key in node.locals:
            attr_node = node.locals[attr_key][0]
            parent = attr_node.parent
            if isinstance(attr_node, nodes.AssignName) and not isinstance(parent, nodes.AnnAssign):
                self.add_message("missing-attribute-type", node=attr_node)
                if self.is_type(attr_node):
                    self.add_message("type-is-assigned", node=attr_node)


def register(linter):
    linter.register_checker(TypeAnnotationChecker(linter))
