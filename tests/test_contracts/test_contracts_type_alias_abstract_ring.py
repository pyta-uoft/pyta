from python_ta.contracts import check_contracts
from tests.test_contracts.test_contracts_type_alias_abstract_network import (
    AbstractNetwork,
)


def test_type_alias_as_type_annotation_for_class_attribute_no_error() -> None:
    @check_contracts
    class AbstractRing(AbstractNetwork):
        def __init__(self) -> None:
            AbstractNetwork.__init__(self)

    AbstractRing()
