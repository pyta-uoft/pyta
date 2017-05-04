"""checker for type inference errors.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from python_ta.transforms.type_inference_visitor import TypeErrorInfo


class TypeInferenceChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'TypeInferenceChecker'
    msgs = {'E9900': ('Type error "%s" inferred',
                      'type-error',
                      'Presented when there is some kind of error with types.'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    @check_messages('type-error')
    def visit_default(self, node):
        if hasattr(node, 'type_constraints'):
            x = node.type_constraints
            if isinstance(x.type, TypeErrorInfo):
                self.add_message('type-error', args=x.type.msg, node=x.type.node)


def register(linter):
    linter.register_checker(TypeInferenceChecker(linter))
