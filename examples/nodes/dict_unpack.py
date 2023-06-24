"""
DictUnpack astroid node

Represents the unpacking of dicts into dicts using PEP 448.

Attributes:
    *This node does not have any explicit attributes*

Example:
    - The double star (**) preceding the dictionary represents dictionary
      unpacking for the nested dictionary. Here is the astroid AST representation
      of them example:
          - Dict(items=[[Const(value=1), Const(value=1)],
                        [DictUnpack(), Dict(items=[[Const(value=2), Const(value=2)]]]]
    - Note that 'DictUnpack()' node is the 'key' and the nested dictionary is
      'value' in the [key, value] pair of the outermost Dict node.

This is node is NOT created when passing a dictionary into a function using ** (e.g. f(**x))

Type-checking:
    - To be documented
"""

# Example 1
{1: 1, **{2: 2}}
