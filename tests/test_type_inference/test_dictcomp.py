import astroid
import nose
from hypothesis import settings, given
from typing import Dict
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


@given(cs.homogeneous_dictionary(min_size=1))
def test_dict_comprehension_single_target_name(dictionary):
    """Test DictComp node visitor representing a comprehension expression with a single target and a
    name expression over a Dictionary."""
    program = f"a = {{key: {dictionary}[key] for key in {dictionary}}}"
    module, TypeInferrer = cs._parse_text(program)
    dictcomp_node = list(module.nodes_of_class(astroid.DictComp))[0]
    assert dictcomp_node.type_constraints.type == dictcomp_node.generators[0].iter.type_constraints.type


if __name__ == '__main__':
    nose.main()
