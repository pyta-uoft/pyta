"""
checker for using constant value in a conditional statement
"""
import astroid

from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class UsingStructureTestChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'using-structure-test'

    msgs = {'E9901': ('%s %s will always return %s, meaning the branch that corresponds'
                      ' to this condition will %s be executed '
                      , 'using-structure-test'
                      , 'Conditional statements should depend on a variable not a constant value.'
                        'This is usually not what the user intended to do')}

    #Collections always return True

    # this is important so that your checker is executed before others
    priority = -1

    def _check_collection(self, node):
        """
        Precondition: node is a condition in an if statement
        Returns true if all the node is a structure/collection of values
        Returns false otherwise
        """
        if isinstance(node, astroid.List) or isinstance(node, astroid.Tuple) or isinstance(node, astroid.Dict) or \
                isinstance(node, astroid.Set):
            return True
    def _is_empty(self, node):
        if not isinstance(node, astroid.Dict):
            return len(node.elts) == 0
        else:
            return len(node.items) == 0

    @check_messages("using-structures-test")
    def visit_if(self, node):
        if self._check_collection(node.test):
            empty = self._is_empty(node.test)
            value = not empty
            if value:
                string = "Non-empty"
            else:
                string = "Empty"
            if value:
                state = "always"
            else:
                state = "never"
            node_type = node.test.name
            if node_type == 'dict':
                node_type = 'dictionary'
            self.add_message('using-structure-test', node=node.test, args=(string, node_type, value, state))
            #self.add_message('using-structure-test', node=node.test, args=(value))


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(UsingStructureTestChecker(linter))
