"""Check for infinite while loops."""

import itertools
from typing import Optional

from astroid import BoundMethod, InferenceError, UnboundMethod, bases, nodes, util
from pylint.checkers import BaseChecker, utils
from pylint.interfaces import INFERENCE
from pylint.lint import PyLinter


class InfiniteLoopChecker(BaseChecker):
    name = "infinite-loop"
    msgs = {
        "W9501": (
            "Infinite while loop: loop does not terminate",
            "infinite-loop",
            """Used when a while loop is guaranteed to never terminate based on its current structure. This usually
            indicates a logical error leading to an unintended infinite loop.""",
        ),
    }

    def visit_while(self, node: nodes.While) -> None:
        checks = [self._check_condition_constant, self._check_condition_all_var_used]
        any(check(node) for check in checks)

    def _check_condition_all_var_used(self, node: nodes.While) -> bool:
        """Helper function that checks whether variables used in a while loop's condition
        are also used anywhere inside the loop body.

        Note: This is a basic check. It only flags loops where NONE of the condition variables
        appear in the body, which indicates an infinite loop.
        """
        # Get variable(s) used inside condition
        cond_vars = set()
        for child in node.test.nodes_of_class(nodes.Name):
            if not isinstance(child.parent, nodes.Call) or child.parent.func is not child:
                cond_vars.add(child.name)
        if not cond_vars:
            return False
        # Check to see if condition variable(s) used inside body
        for child in node.body:
            for name_node in child.nodes_of_class((nodes.Name, nodes.AssignName)):
                if name_node.name in cond_vars:
                    # At least one condition variable is used in the loop body
                    return False
        else:
            self.add_message(
                "infinite-loop",
                node=node.test,
            )
            return True

    def _check_condition_constant(self, node: nodes.While) -> bool:
        """Helper function that checks if a constant while-loop condition may lead to an infinite loop.

        This helper flags loops that meet **both** of the following criteria:
            - The `while` condition is constant (e.g., `while 1 < 2`)
            - The loop body contains no `return`, `break`, `raise`, `yield`, or `sys.exit()` calls
        """
        if not self._check_constant_loop_cond(
            node.test
        ) and not self._check_constant_form_condition(node):
            return False
        inferred = utils.safe_infer(node.test)
        if isinstance(inferred, util.UninferableBase) or inferred is None:
            return False
        if (
            (isinstance(inferred, nodes.Const) and bool(inferred.value) is False)
            or (isinstance(inferred, (nodes.List, nodes.Tuple, nodes.Set)) and not inferred.elts)
            or (isinstance(inferred, nodes.Dict) and not inferred.items)
        ):
            return False

        check_nodes = (nodes.Break, nodes.Return, nodes.Raise, nodes.Yield)
        for child in node.body:
            for exit_node in child.nodes_of_class(klass=(nodes.Call, *check_nodes)):
                if isinstance(exit_node, check_nodes):
                    return False
                # Check Call node to see if `sys.exit()` is called
                elif (
                    isinstance(exit_node, nodes.Call)
                    and isinstance(exit_node.func, nodes.Attribute)
                    and exit_node.func.attrname == "exit"
                ):
                    inferred = utils.safe_infer(exit_node.func.expr)
                    if (
                        not isinstance(inferred, util.UninferableBase)
                        and inferred is not None
                        and isinstance(inferred, nodes.Module)
                        and inferred.name == "sys"
                    ):
                        return False
        else:
            self.add_message("infinite-loop", node=node.test, confidence=INFERENCE)
            return True

    def _check_constant_form_condition(self, node: nodes.While) -> bool:
        """Helper function that checks if while loop condition is of constant form (e.g.: `1 < 2`, `5 - 1 >= 2 + 2`)"""
        return not any(node.test.nodes_of_class(nodes.Name))

    def _check_constant_loop_cond(self, test_node: Optional[nodes.NodeNG]) -> bool:
        """Helper function that checks if while loop condition is constant.

        See `https://github.com/pylint-dev/pylint/blob/main/pylint/checkers/base/basic_checker.py#L303` for further
        detail."""
        const_nodes = (
            nodes.Module,
            nodes.GeneratorExp,
            nodes.Lambda,
            nodes.FunctionDef,
            nodes.ClassDef,
            bases.Generator,
            UnboundMethod,
            BoundMethod,
        )
        structs = (nodes.Dict, nodes.Tuple, nodes.Set, nodes.List)
        except_nodes = (
            nodes.Call,
            nodes.BinOp,
            nodes.BoolOp,
            nodes.UnaryOp,
            nodes.Subscript,
        )
        inferred = None
        maybe_generator_call = None
        emit = isinstance(test_node, (nodes.Const, *structs, *const_nodes))
        if not isinstance(test_node, except_nodes):
            inferred = utils.safe_infer(test_node)
            # If we can't infer what the value is but the test is just a variable name
            if isinstance(inferred, util.UninferableBase) and isinstance(test_node, nodes.Name):
                emit, maybe_generator_call = InfiniteLoopChecker._name_holds_generator(test_node)

        # Emit if calling a function that only returns GeneratorExp (always tests True)
        elif isinstance(test_node, nodes.Call):
            maybe_generator_call = test_node

        if maybe_generator_call:
            inferred_call = utils.safe_infer(maybe_generator_call.func)
            if isinstance(inferred_call, nodes.FunctionDef):
                # Can't use all(x) or not any(not x) for this condition, because it
                # will return True for empty generators, which is not what we want.
                all_returns_were_generator = None
                for return_node in inferred_call._get_return_nodes_skip_functions():
                    if not isinstance(return_node.value, nodes.GeneratorExp):
                        all_returns_were_generator = False
                        break
                    all_returns_were_generator = True
                if all_returns_were_generator:
                    return True
        if emit:
            return True
        elif isinstance(inferred, const_nodes):
            return True
        return False

    @staticmethod
    def _name_holds_generator(test_node: nodes.Name) -> tuple[bool, Optional[nodes.Call]]:
        """Return whether `test` tests a name certain to hold a generator, or optionally
        a call that should be then tested to see if *it* returns only generators.

        See `https://github.com/pylint-dev/pylint/blob/main/pylint/checkers/base/basic_checker.py#L303` for further
        detail."""
        assert isinstance(test_node, nodes.Name)
        emit = False
        maybe_generator_call = None
        lookup_result = test_node.frame().lookup(test_node.name)
        if not lookup_result:
            return emit, maybe_generator_call
        maybe_generator_assigned = (
            isinstance(assign_name.parent.value, nodes.GeneratorExp)
            for assign_name in lookup_result[1]
            if isinstance(assign_name.parent, nodes.Assign)
        )
        first_item = next(maybe_generator_assigned, None)
        if first_item is not None:
            # Emit if this variable is certain to hold a generator
            if all(itertools.chain((first_item,), maybe_generator_assigned)):
                emit = True
            # If this variable holds the result of a call, save it for next test
            elif (
                len(lookup_result[1]) == 1
                and isinstance(lookup_result[1][0].parent, nodes.Assign)
                and isinstance(lookup_result[1][0].parent.value, nodes.Call)
            ):
                maybe_generator_call = lookup_result[1][0].parent.value
        return emit, maybe_generator_call


def register(linter: PyLinter) -> None:
    linter.register_checker(InfiniteLoopChecker(linter))
