import tabulate


class AccumulationTable:
    _num_iterations: int
    _accumulation_names: list
    _loop_accumulation_values: dict
    _loop_var_name: str
    _loop_variable: list

    def __init__(self, accumulation_names: list, first_accumulation: list, loop_var_name: str):
        self._num_iterations = 0
        self._accumulation_names = accumulation_names
        self._loop_accumulation_values = {}
        for i in range(len(accumulation_names)):
            self._loop_accumulation_values[accumulation_names[i]] = [first_accumulation[i]]
        self._loop_var_name = loop_var_name
        self._loop_variable = ["N/A"]

    def add_iteration(self, val: list, var) -> None:
        self._loop_variable.append(var)
        for i in range(len(self._accumulation_names)):
            self._loop_accumulation_values[self._accumulation_names[i]].append(val[i])
        self._num_iterations += 1

    def convert_table(self) -> dict:
        table_dict = {
            "iterations": list(range(self._num_iterations + 1)),
            "loop variable (" + self._loop_var_name + ")": self._loop_variable,
        }
        for key, pair in self._loop_accumulation_values.items():
            table_dict[key] = pair
        return table_dict

    def tabulate_data(self) -> None:
        print(
            tabulate.tabulate(
                self.convert_table(), headers="keys", colalign=("left", "left", "left")
            )
        )

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.tabulate_data()
