"""checker for bad indexing in a loop.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from typing import List, Optional
from astroid.node_classes import NodeNG


class BadLoopIndexingChecker(BaseChecker):
    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'bad_loop_indexing'
    # use dashes for connecting words in message symbol
    msgs = {'E9994': (f'Bad use of loop variable %s in for loop',
                      'bad-loop-indexing',
                      'Used when you have an loop variable in a for loop '
                      'where its only usage is to index the iterable'),
            }

    # this is important so that your checker is executed before others
    priority = -1

    # pass in message symbol as a parameter of check_messages
    @check_messages("bad-loop-indexing")
    def visit_for(self, node: astroid.For) -> None:
        if self._is_bad_loop_indexing(node):
            args = f"'{node.target.name}'"
            self.add_message('bad-loop-indexing', node=node.target, args=args)

    def _is_bad_loop_indexing(self, node: astroid.For) -> bool:
        """Return whether the usage of the indexing variable in the for loop is ONLY to index the iterable.
        True if bad, False if not bad.
        """
        # Store the iteration variable
        index = node.target.name

        # Check if the iterable of the for-loop is of the form "range(len(lst))"
        iterable = _iterable_if_range(node.iter)
        if iterable is None:
            return False

        lst_index_nodes = _index_name_nodes(node, index)
        return not any(_is_correct_usage__of_index(index_node, iterable) for index_node in lst_index_nodes) \
               and lst_index_nodes


# Helper functions
def _iterable_if_range(node: Optional[NodeNG]) -> Optional[str]:
    """Return the string of the iterable if this node is of the form: range(len(iterable)).
    Return None otherwise.
    """
    # Order of operations is important
    if isinstance(node, astroid.Call):
        if isinstance(node.func, astroid.Name) and node.func.name == 'range' \
                and isinstance(node.args[0], astroid.Call) \
                and isinstance(node.args[0].func, astroid.Name) and node.args[0].func.name == 'len':
            return node.args[0].args[0].name
            # if node is None, returns None


def _is_correct_usage__of_index(index_node: astroid.Name, iterable: str) -> bool:
    """Return whether or not <index> was used appropriately in the for loop.
    Return True if used appropriately, False if badly used.
    """
    # Name node is not inside Subscript node iterable[index]
    if not (isinstance(index_node.parent, astroid.Index) and isinstance(index_node.parent.parent, astroid.Subscript)
            and index_node.parent.parent.value.name == iterable):
        return True

    # Use subscript.ctx attribute to find out what context it is being used in.
    subscript_node = index_node.parent.parent
    return subscript_node.ctx == astroid.Store


def _index_name_nodes(node: astroid.For, index: str) -> List[astroid.Name]:
    """Return a list of <index> Name nodes contained in <node>."""
    return [name_node for name_node in node.nodes_of_class(astroid.Name) if name_node.name == index]


def register(linter):
    linter.register_checker(BadLoopIndexingChecker(linter))
