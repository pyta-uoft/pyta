"""checker for type annotation.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker


class TypeAnnotationChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'TypeAnnotationChecker'
    msgs = {'E9970': ('Function parameter is missing type annotation',
                      'type-annotation-param',
                      'Presented when a type annotation is missing.'),
            'E9971': ('Function is missing return type annotation',
                      'type-annotation-return',
                      'Presented when a type annotation is missing.'),
            'E9972': ('Variable is missing type annotation',
                      'type-annotation-var',
                      'Presented when a type annotation is missing.'),
            'E9973': ('Instance variable should be annotated in class body',
                      'type-annotation-inst-var',
                      'Presented when a type annotation is missing.'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    def visit_functiondef(self, node):
        for i in range(len(node.args.annotations)):
            if node.args.annotations[i] is None:
                # Check if function is a non-static instance method
                if i != 0 or not isinstance(node.parent, astroid.ClassDef) or node.type == 'staticmethod':
                    self.add_message('type-annotation-param', node=node.args.args[i])

        if node.returns is None:
            self.add_message('type-annotation-return', node=node.args)

    def visit_classdef(self, node):
        for attr_key in node.instance_attrs:
            annotated(attr_key, node)

        for attr_key in node.locals:
            attr_node = node.locals[attr_key][0]
            if isinstance(attr_node, astroid.AssignName) and not isinstance(attr_node.parent, astroid.AnnAssign):
                self.add_message('type-annotation-var', node=attr_node)


def annotated(attr_key, node):
    if attr_key in node.instance_attrs:
        attr_node = node.instance_attrs[attr_key][0]
        if len(node.bases) == 0:
            if isinstance(attr_node, astroid.AssignAttr):
                if attr_key not in node.locals:
                    return False
                elif isinstance(attr_node.parent, astroid.AnnAssign):
                    return False
            return True
        else:
            return any(annotated(attr_key, parent_node) for parent_name in node.bases
                       for parent_node in node.parent.globals[parent_name.name])

def register(linter):
    linter.register_checker(TypeAnnotationChecker(linter))
