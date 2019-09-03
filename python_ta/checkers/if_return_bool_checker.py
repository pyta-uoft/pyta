import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class IfReturnBoolChecker(BaseChecker):

    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'if_return_bool'
    # use dashes for connecting words in message symbol
    msgs = {'E9990': ('This can be simplified to something like `return {if-condition}`.',
                      'if_return_bool',
                      'Reported if there is only one statment in an If statment that '
                      'is a boolean return statement'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    # pass in message symbol as a parameter of check_messages
    @check_messages('if_return_bool')
    def visit_if(self, node: astroid.If):
        if not isinstance(node.scope(), astroid.FunctionDef):
            return

        # should we require if body/orelse to have only one statement
        # any statment after return is unreachable anyways?
        for n in (node.body[0], node.orelse[0]):
            if isinstance(n, astroid.Return) \
                    and isinstance(n.value, astroid.Const) \
                    and n.value.value in (True, False):
                continue
            break
        else:
            self.add_message('if_return_bool', node=node)


def register(linter):
    linter.register_checker(IfReturnBoolChecker(linter))
