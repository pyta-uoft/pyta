"""checker for type inference errors.
"""

import astroid
from typing import _ForwardRef
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from python_ta.transforms.type_inference_visitor import TypeInferer
from python_ta.typecheck.base import TypeFail, TypeFailLookup, TypeFailUnify


class TypeInferenceChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'TypeInferenceChecker'
    msgs = {'E7700': ('%s',
                      'type-error',
                      'Presented when there is some kind of error with types.'),
            'E7701': ('Type Error inferred between %s and %s',
                      'type-error-unify',
                      'Presented when there is a unification error between types.'),
            'E7702': ('Lookup Error inferred',
                      'type-error-lookup',
                      'Presented when there is a lookup error.'),
            }

    # this is important so that your checker is executed before others
    priority = -1

    def __init__(self, linter):
        self.type_fails = []
        super().__init__(linter)

    @check_messages('type-error')
    def visit_default(self, node):
        if hasattr(node, 'inf_type') and isinstance(node.inf_type, TypeFail) and node.inf_type not in self.type_fails:
            self.type_fails.append(node.inf_type)

            if isinstance(node.inf_type, TypeFailUnify):
                args = []
                for tn in node.inf_type.tnodes:
                    if tn.ast_node:
                        args.append(tn.ast_node.as_string())
                    elif isinstance(tn.type, _ForwardRef):
                        args.append(str(tn.type))
                    elif tn.type is not None:
                        args.append(tn.type.__name__)
                    else:
                        args.append(tn.type)
                self.add_message('type-error-unify', args=tuple(args), node=node.inf_type.src_node)
            elif isinstance(node.inf_type, TypeFailLookup):
                self.add_message('type-error-lookup', node=node.inf_type.src_node)
            else:
                self.add_message('type-error', args=node.inf_type, node=node)


def register(linter):
    linter.register_checker(TypeInferenceChecker(linter))
