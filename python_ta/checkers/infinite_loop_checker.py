"""Check for infinite while loops."""

import itertools

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
        self._check_condition_constant(node)
        self._check_condition_all_var_used(node)

    def _check_condition_all_var_used(self, node: nodes.While) -> None:
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
            return
        # Check to see if condition variable(s) used inside body
        for child in node.body:
            for name_node in child.nodes_of_class((nodes.Name, nodes.AssignName)):
                if name_node.name in cond_vars:
                    # At least one condition variable is used in the loop body
                    return
        else:
            self.add_message(
                "infinite-loop",
                node=node.test,
            )

    def _check_condition_constant(self, node: nodes.While) -> None:
        """Helper function that checks if a constant while-loop condition may lead to an infinite loop.

        This helper flags loops that meet **both** of the following criteria:
            - The `while` condition is constant (e.g., `while 1 < 2`)
            - The loop body contains no `return`, `break`, `raise`, `yield`, or `sys.exit()` calls
        """
        if not self._check_constant_loop_cond(node, node.test):
            return
        check_nodes = (nodes.Break, nodes.Return, nodes.Raise, nodes.Yield)
        inference_used = False
        for child in node.body:
            for exit_node in child.nodes_of_class(klass=(nodes.Call, *check_nodes)):
                if isinstance(exit_node, check_nodes):
                    return
                # Check Call node to see if `sys.exit()` is called
                elif (
                    isinstance(exit_node, nodes.Call)
                    and isinstance(exit_node.func, nodes.Attribute)
                    and exit_node.func.attrname == "exit"
                ):
                    if (
                        isinstance(exit_node.func.expr, nodes.Name)
                        and exit_node.func.expr.name == "sys"
                    ):
                        return
                    else:
                        inference_used = True
                        inferred = utils.safe_infer(exit_node.func.expr)
                        if (
                            not isinstance(inferred, util.UninferableBase)
                            and inferred is not None
                            and inferred.name == "sys"
                        ):
                            return
        else:
            if not inference_used:
                self.add_message(
                    "infinite-loop",
                    node=node.test,
                )
            else:
                self.add_message("infinite-loop", node=node.test, confidence=INFERENCE)

    def _check_constant_loop_cond(self, node: nodes.While, test: nodes.NodeNG | None) -> bool:
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
            # nodes.BoolOp,
            nodes.UnaryOp,
            nodes.Subscript,
        )
        inferred = None
        maybe_generator_call = None
        emit = isinstance(test, (nodes.Const, *structs, *const_nodes))
        if not isinstance(test, except_nodes):
            inferred = utils.safe_infer(test)
            # If we can't infer what the value is but the test is just a variable name
            if isinstance(inferred, util.UninferableBase):
                if isinstance(test, nodes.Name):
                    emit, maybe_generator_call = InfiniteLoopChecker._name_holds_generator(test)
            else:
                if (
                    inferred is not None
                    and isinstance(inferred, nodes.Const)
                    and bool(inferred.value) is True
                ):
                    cond_vars = set(child for child in node.test.nodes_of_class(nodes.Name))
                    if not cond_vars:
                        emit = True

        # Emit if calling a function that only returns GeneratorExp (always tests True)
        elif isinstance(test, nodes.Call):
            maybe_generator_call = test

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
            # If the constant node is a FunctionDef or Lambda then
            # it may be an illicit function call due to missing parentheses
            call_inferred = None
            try:
                # Just forcing the generator to infer all elements.
                # astroid.exceptions.InferenceError are false positives
                if isinstance(inferred, nodes.FunctionDef):
                    call_inferred = list(inferred.infer_call_result(node))
                elif isinstance(inferred, nodes.Lambda):
                    call_inferred = list(inferred.infer_call_result(node))
            except InferenceError:
                call_inferred = None
            if call_inferred:
                # Function pointer is not considered constant in our case (e.g.: `while func_pointer`) even
                # if it results in the loop condition always being true.
                return False
            return True
        return False

    @staticmethod
    def _name_holds_generator(test: nodes.Name) -> tuple[bool, nodes.Call | None]:
        """Return whether `test` tests a name certain to hold a generator, or optionally
        a call that should be then tested to see if *it* returns only generators.
        """
        assert isinstance(test, nodes.Name)
        emit = False
        maybe_generator_call = None
        lookup_result = test.frame().lookup(test.name)
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
