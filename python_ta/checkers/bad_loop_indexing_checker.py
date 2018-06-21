"""checker for bad indexing in a loop.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from typing import List


class BadLoopIndexingChecker(BaseChecker):
    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'bad_loop_indexing'
    # use dashes for connecting words in message symbol
    msgs = {'E9994': ('Bad loop indexing used in this for-loop',
                      'bad-loop-indexing',
                      'Used when you have an iteration variable in a for-loop '
                      'where its only usage is to index the iterable it is iterating over'),
            }

    # this is important so that your checker is executed before others
    priority = -1

    def _check_bad_loop_indexing(self, node):
        """Return whether the usage of the indexing variable in the for-loop is ONLY to index the iterable.
        True if bad, False if not bad.
        """
        # Store the iteration variable
        index = node.target.name

        # Check if the iterable of the for-loop is of the form "range(len(lst))"
        iterable_lst = _check_iterable_is_range(node)
        if iterable_lst:
            iterable = iterable_lst[0]
        else:
            return False

        # Use node_of_class to find all Name nodes.
        if any(_check_correct_usage(name_node, index, iterable) for name_node in node.nodes_of_class(astroid.Name)):
            return False
        # There is at least one 'index' Name node and they are all used badly.
        elif any(name_node.name == index for name_node in node.nodes_of_class(astroid.Name)):
            return True
        # There are no 'index' Name nodes.
        # Bad-loop-indexing checker should not catch an error since this is a case for
        # checker W0612(unused-variable) to prevent duplicating error detection.
        else:
            return False

    # pass in message symbol as a parameter of check_messages
    @check_messages("bad-loop-indexing")
    def visit_for(self, node):
        if self._check_bad_loop_indexing(node):
            self.add_message('bad-loop-indexing', node=node)


# Helper functions
def _check_iterable_is_range(node: astroid.For) -> List[str]:
    """Return a list containing the iterable of this For node if it is of the form: range(len(iterable)).
    Return an empty list if it is not of this form.
    """
    _iter = node.iter
    # Order of operations is important
    if isinstance(_iter, astroid.Call) and isinstance(_iter.func, astroid.Name) \
            and _iter.func.name == 'range' and isinstance(_iter.args[0], astroid.Call) \
            and isinstance(_iter.args[0].func, astroid.Name) and _iter.args[0].func.name == 'len':
        return [_iter.args[0].args[0].name]
    else:
        return []


def _check_correct_usage(node: astroid.Name, index: str, iterable: str) -> bool:
    """Return whether or not this Name node 'index' was used correctly in the for loop.
    Return True if correctly used, False if badly used or node is not 'index'.
    """
    # If Name node is 'index'
    if node.name == index:
        # If Name node is inside Subscript node iterable[index]
        if isinstance(node.parent, astroid.Index) and isinstance(node.parent.parent, astroid.Subscript) \
                and node.parent.parent.value.name == iterable:
            subscript_node = node.parent.parent
            # iterable[index] (eg. lst[i]) used in the left side of an assignment
            # Assign node of form "a = b = 1"
            if isinstance(subscript_node.parent, astroid.Assign):
                if any(target == subscript_node for target in subscript_node.parent.targets):
                    return True
            # Assign node of form "a, b = 1, 2"
            elif isinstance(subscript_node.parent, astroid.Tuple) and \
                    isinstance(subscript_node.parent.parent, astroid.Assign):
                if any(target == subscript_node for target in subscript_node.parent.parent.targets[0].elts):
                    return True
            # AugAssign node
            elif isinstance(subscript_node.parent, astroid.AugAssign):
                if subscript_node == subscript_node.parent.target:
                    return True
            # 1)iterable[index] not used on the left side of Assign/AugAssign statement (eg. s += iterable[index])
            # 2)iterable[index] not used as part of Assign/AugAssign statement (eg. if iterable[index] % 2 == 0:)
            return False
        # Name node is not inside Subscript node iterable[index]
        else:
            return True
    else:
        return False


def register(linter):
    linter.register_checker(BadLoopIndexingChecker(linter))
