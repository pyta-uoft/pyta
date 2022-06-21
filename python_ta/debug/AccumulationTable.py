import inspect

import astroid
import tabulate


class AccumulationTable:
    _num_iterations: int
    _accumulation_names: list
    _loop_accumulation_values: dict
    _loop_var_name: str
    _loop_variable: list

    def __init__(self, accumulation_names: list):
        self._accumulation_names = accumulation_names
        self._num_iterations = 0
        self._loop_variable = ["N/A"]

    def add_iteration(self, val: list, var) -> None:
        self._loop_variable.append(var)
        for i in range(len(self._accumulation_names)):
            self._loop_accumulation_values[self._accumulation_names[i]].append(val[i])
        self._num_iterations += 1

    def _convert_table(self) -> dict:
        table_dict = {
            "iterations": list(range(self._num_iterations + 1)),
            "loop variable (" + self._loop_var_name + ")": self._loop_variable,
        }
        for key, pair in self._loop_accumulation_values.items():
            table_dict[key] = pair
        return table_dict

    def _tabulate_data(self) -> None:
        print(
            tabulate.tabulate(
                self._convert_table(), headers="keys", colalign=("left", "left", "left")
            )
        )

    def _loop_string(self, nconverted: str) -> str:
        list_str = nconverted.split("\n")
        temp_index = 0
        for i in range(len(list_str)):
            if "for" in list_str[i] and "in" in list_str[i]:
                temp_index = i
                break

        cut_s = list_str[temp_index:]
        curr_str = ""
        for elem in cut_s:
            curr_str += elem + "\n"

        return curr_str

    def _add_keys(self, ast_node, prev) -> None:
        self._loop_var_name = ast_node.target.name
        self._loop_accumulation_values = {}
        for name in self._accumulation_names:
            if name in prev.f_locals:
                self._loop_accumulation_values[name] = [prev.f_locals[name]]

    def __enter__(self):
        prev = inspect.getouterframes(inspect.currentframe())[1].frame
        cdoc = inspect.cleandoc(inspect.getsource(prev))
        loop_str = self._loop_string(cdoc)
        ast_node = astroid.parse(loop_str).body[0]
        self._add_keys(ast_node, prev)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self._tabulate_data()
