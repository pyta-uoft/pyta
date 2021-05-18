import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from ast import literal_eval


class InvalidRangeIndexChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'invalid_range_index'
    msgs = {'E9993':
                ('You should not use invalid range index on line %s',
                 'invalid-range-index',
                 'Used when you use invalid index range')}
    # this is important so that your checker is executed before others
    priority = -1

    @check_messages("invalid-range-index")
    def visit_call(self, node):
        if isinstance(node.func, astroid.Name):
            name = node.func.name
            # ignore the name if it's not a builtin (i.e. not defined in the
            # locals nor globals scope)
            if (not (name in node.frame() or name in node.root()) and
                            name == 'range'):
                arg = node.args  # the arguments of 'range' call
                # guard nodes (e.g. Name) not properly handled by literal_eval.
                if any([not isinstance(item, astroid.Const) for item in arg]):
                    return
                eval_parm = list(map(lambda z: literal_eval(z.as_string()), arg))

                # check if there is no args in 'range' call
                if (len(arg) == 0 or
                    not all([isinstance(c, int) for c in eval_parm]) or
                    (len(arg) == 1 and eval_parm[0] < 2) or
                    (len(arg) == 2 and eval_parm[1] - eval_parm[0] < 2)):

                    args = "{}".format(node.lineno)
                    self.add_message('invalid-range-index', node=node,
                                 args=args)

                if len(arg) == 3:
                    if (abs(eval_parm[2]) >= abs(eval_parm[0] - eval_parm[1]) or
                    eval_parm[2] == 0 or
                    (eval_parm[0] > eval_parm[1] and eval_parm[2] < 0) or
                    (eval_parm[0] < eval_parm[1] and eval_parm[2] > 0)):

                        args = "{}".format(node.lineno)
                        self.add_message('invalid-range-index', node=node,
                                 args=args)


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(InvalidRangeIndexChecker(linter))
