from astroid import nodes
from hypothesis import HealthCheck, assume, given, settings

from .. import custom_hypothesis_support as cs

settings.load_profile("pyta")


@given(cs.const_node())
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_const(node):
    """Test Const nodes representing int, bool, float, and None literal values.

    NOTE: string literals aren't checked here because it seems that astroid doesn't
    parse modules that contain only a single string literal.
    """
    assume(not isinstance(node.value, str))
    module, _ = cs._parse_text(node)
    cs._verify_type_setting(module, nodes.Const, type(node.value))
