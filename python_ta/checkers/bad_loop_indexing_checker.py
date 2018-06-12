"""checker for bad indexing in a loop.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


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
        # store the iteration variable
        index = node.target.name

        # check if the iterable of the for-loop is of the form "range(len(lst))"
        if isinstance(node.iter, astroid.Call):
            _iter = node.iter
            if isinstance(_iter.func, astroid.Name):
                if _iter.func.name == 'range' and isinstance(_iter.args[0], astroid.Call):
                    _iter2 = _iter.args[0]
                    if isinstance(_iter2.func, astroid.Name) and _iter2.func.name == 'len':
                        iterable = _iter2.args[0].name
                    else:
                        return False
                else:
                    return False
            # _iter.func is Attribute node
            else:
                return False
        else:
            return False

        # use nodes_of_class to find Name nodes
        for node in node.nodes_of_class(astroid.Name):
            if node.name == index:
                if isinstance(node.parent, astroid.Index):
                    if isinstance(node.parent.parent, astroid.Subscript):
                        subscript_node = node.parent.parent
                        if subscript_node.value.name == iterable:
                            # iterable[index] (eg. lst[i]) used in the left side of an assignment
                            # Assign node of form "a = b = 1"
                            if isinstance(subscript_node.parent, astroid.Assign):
                                if any(target == subscript_node for target in subscript_node.parent.targets):
                                    return False
                                else:
                                    return True
                            # Assign node of form "a, b = 1, 2"
                            elif isinstance(subscript_node.parent, astroid.Tuple):
                                if isinstance(subscript_node.parent.parent, astroid.Assign):
                                    if any(target == subscript_node for target in
                                           subscript_node.parent.parent.targets[0].elts):
                                        return False
                                    else:
                                        return True
                            # AugAssign node
                            elif isinstance(subscript_node.parent, astroid.AugAssign):
                                if subscript_node == subscript_node.parent.target:
                                    return False
                                else:
                                    return True
                            # iterable[index] not used in the left side of an assignment ie. bad usage
                            else:
                                return True
                # It will pass through to here if node.name == index but not subscript_node.slice.name == iterable
                # ie. if Name node with <index> is found but not used in the form of <iterable[index]>
                return False
            # else:
            # go to the next Name node
        # If all Name nodes are searched but none of them are <index> which means the indexing variable was not used.
        # There already is an unused variable checker to catch this error.
        # TODO: is it sufficient to only search for the indexing variable in the Name nodes???
        return False

    # pass in message symbol as a parameter of check_messages
    @check_messages("bad-loop-indexing")
    def visit_for(self, node):
        if self._check_bad_loop_indexing(node):
            self.add_message('bad-loop-indexing', node=node)


def register(linter):
    linter.register_checker(BadLoopIndexingChecker(linter))
