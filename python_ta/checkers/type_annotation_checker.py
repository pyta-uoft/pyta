"""checker for type annotation.
"""

import builtins

from astroid import nodes
from astroid.exceptions import NoDefault
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from pylint.interfaces import IAstroidChecker

builtin_types = []
for name in dir(builtins):
    candidate = getattr(builtins, name)
    if isinstance(candidate, type):
        builtin_types.append(name)


class TypeAnnotationChecker(BaseChecker):

    __implements__ = IAstroidChecker

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

    @check_messages("missing-param-type", "type-is-assigned", "missing-return-type")
    def visit_functiondef(self, node):
        arguments = node.args.arguments
        names = [arg.name for arg in arguments if isinstance(arg, nodes.AssignName)]
        for name in names:
            # Check if assign builtin
            try:
                default_value = node.args.default_value(name)
            except NoDefault:
                continue
            if isinstance(default_value, nodes.Name) and default_value.name in builtin_types:
                self.add_message("type-is-assigned", node=node.args.find_argname(name)[1])

        annotations = node.args.annotations
        for i in range(len(annotations)):
            if annotations[i] is None:
                # Check if function is a non-static instance method
                if (
                    i != 0
                    or not isinstance(node.parent, nodes.ClassDef)
                    or node.type == "staticmethod"
                ):
                    self.add_message("missing-param-type", node=node.args.args[i])

        if node.returns is None:
            self.add_message("missing-return-type", node=node.args)

    @check_messages("missing-attribute-type")
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
                # Check if assign builtin
                if isinstance(parent, nodes.Assign) and isinstance(parent.value, nodes.Name):
                    if parent.value.name in builtin_types:
                        self.add_message("type-is-assigned", node=attr_node)


def register(linter):
    linter.register_checker(TypeAnnotationChecker(linter))
