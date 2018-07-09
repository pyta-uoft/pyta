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
        # Store the iteration variable.
        index = node.target.name

        # Check if the iterable of the for loop is of the form "range(len(lst))".
        iterable = _iterable_if_range(node.iter)
        if iterable is None:
            return False

        # AugAssign is special (i += 2 is actually i = i + 2).
        # Check if any AssignName nodes in an AugAssign node refers to the iteration variable.
        if any(index_node.lookup(index)[1][0] == node.target for index_node in _augassign_index_nodes(node, index)):
            return False
        # i) For all index_node in augassign_index_nodes, .lookup != node.target, so they are all rebound
        # or ii) there are no AugAssign nodes.
        return not any(index_node.lookup(index)[1][0] == node.target
                       for index_node in _good_use_index_nodes(node, index)) \
            and (_index_assign_name_nodes(node, index) or _index_name_nodes(node, index))


# Helper functions
def _iterable_if_range(node: Optional[NodeNG]) -> Optional[str]:
    """Return the string of the iterable if this node is of the form: range(len(iterable)).
    Return None otherwise.
    """
    # Order of operations is important.
    if isinstance(node, astroid.Call):
        if isinstance(node.func, astroid.Name) and node.func.name == 'range' \
                and isinstance(node.args[0], astroid.Call) \
                and isinstance(node.args[0].func, astroid.Name) and node.args[0].func.name == 'len':
            return node.args[0].args[0].name
            # If node is None, returns None.


def _is_correct_usage_of_index(index_node: astroid.Name, for_node: astroid.For) -> bool:
    """Return whether or not <index_node> was used appropriately in <for_node>.
    Return False if used only to index the iterable or rebound. Otherwise, return True.
    """
    iterable = _iterable_if_range(for_node.iter)
    # Name node is not inside Subscript node iterable[index].
    if not (isinstance(index_node.parent, astroid.Index) and isinstance(index_node.parent.parent, astroid.Subscript)
            and index_node.parent.parent.value.name == iterable):
        return True
    # Use subscript.ctx attribute to find out what context it is being used in.
    subscript_node = index_node.parent.parent
    return subscript_node.ctx == astroid.Store


def _augassign_index_nodes(for_node: astroid.For, index: str) -> List[astroid.AssignName]:
    """Return a list of <index> AssignName nodes that are in AugAssign nodes in <for_node>."""
    return [as_name_node for as_name_node in _index_assign_name_nodes(for_node, index)
            if isinstance(as_name_node.parent, astroid.AugAssign)]


def _good_use_index_nodes(for_node: astroid.For, index: str) -> List[astroid.Name]:
    """Return a list of <index> Name nodes that used not only to index the iterable in <for_node>,
    e.g., lst[index] = 2, s += index, i = (i+1)//2, and for i in range(lst[i//2])."""
    return [name_node for name_node in _index_name_nodes(for_node, index)
            if _is_correct_usage_of_index(name_node, for_node)]


def _index_name_nodes(for_node: astroid.For, index: str) -> List[astroid.Name]:
    """Return a list of <index> Name nodes contained in <for_node>."""
    return [name_node for name_node in for_node.nodes_of_class(astroid.Name) if name_node.name == index]


def _index_assign_name_nodes(for_node: astroid.For, index: str) -> List[astroid.AssignName]:
    """Return a list of <index> AssignName nodes contained in the body of <for_node>."""
    return [as_name_node for as_name_node in for_node.nodes_of_class(astroid.AssignName) if as_name_node.name == index
            and as_name_node != for_node.target]


def register(linter):
    linter.register_checker(BadLoopIndexingChecker(linter))
