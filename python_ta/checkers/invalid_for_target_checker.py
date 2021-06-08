"""Checker for target of for loop in subscript form.
"""
from typing import Union

import astroid
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from pylint.interfaces import IAstroidChecker


class InvalidForTargetChecker(BaseChecker):
    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'invalid_for_target'
    # use dashes for connecting words in message symbol
    msgs = {'E9984': ('For loop variable "%s" should not be a part of a larger object.',
                      'invalid-for-target',
                      'Used when you have a loop variable in a for loop '
                      'that is in subscript or object attribute form'),
            }
    # this is important so that your checker is executed before others
    priority = -1
    # pass in message symbol as a parameter of check_messages

    INVALID_TARGETS = (astroid.Subscript, astroid.AssignAttr)

    @check_messages('invalid-for-target')
    def visit_for(self, node: astroid.For) -> None:

        for_targets = _unnest_recursive_seq(node.target)
        for target in for_targets:
            if isinstance(target, self.INVALID_TARGETS):
                self.add_message('invalid-for-target',
                                 node=target, args=target.as_string())


def _unnest_recursive_seq(node: Union[astroid.List,
                                      astroid.Tuple,
                                      astroid.node_classes.NodeNG]) -> \
        list[astroid.node_classes.NodeNG]:
    """Return a list of all non-List/Tuple nodes contained in node

    Note: passing in an astroid.For node directly will just return the node;
    pass in the .target get the list of all targets.
    """

    if isinstance(node, (astroid.List, astroid.Tuple)):
        nested_targets = []
        for nested_node in node.elts:
            nested_targets += _unnest_recursive_seq(nested_node)
        return nested_targets
    else:
        return [node]


def register(linter):
    linter.register_checker(InvalidForTargetChecker(linter))
