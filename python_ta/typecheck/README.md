# Typechecking status


## Nodes
**TODOs:**
- Think of better ways of representing objects when returning error messages from typechecking.

### Assign

Done.

### BinOp

Done.

### BoolOp

Done.

### Call

**TODOs:**
* Handling inheritance

### ClassDef

**TODOs:**
- Look into instance_attrs vs locals for ClassDef nodes
- Handle class variables (and corresponding type annotations)
- Refactor to remove code duplication in updating TypeStore

### Compare

Done.

### Comprehension

Done.

### Const
Done.

### Dict

**TODOs:** see List.

### DictComp

Done.

### For

Done.

### FunctionDef

**TODOs:**
- Distinguish between different types of methods (instance, static, class)

### GeneratorExp

Done.

### IfExp

Done.

### Index

Done.

### List

**TODOs:**
- Represent the type of an empty list.
- Flag to require homogeneity (?)
- Lists in assignment ("Store") context
- Better articulate Any vs. Object

### ListComp

Done.

### Name

**TODOs:**
- unify lookup approaches for builtins vs. user-defined variables.

### Set

**TODOs:** see List.

### SetComp

Done.

### Slice

Done.

### Subscript

**TODOs:**
- Handle ExtSlice

### Tuple

Done.

### UnaryOp

Done.


## Type Inference

### New Error Type
- Edit TypeFail to include new attributes src_node, tnode1, tnode2
- Edit _TNode to include new attributes ast_node, ctx_node
- Edit unify to:
  - Take as an argument the astroid node in which the unification is taking place
  - Return TypeFail with new attributes
- Edit all functions that use resolve, unify, _merge_sets, _assign_type, _handle_call to be properly monadic

### Other
- Rename _make_set to better reflect functionality
- Remove duplicated functionality between unify, _unify_generic and unify_call
- Remove all instances of .getValue()
- Unify functionality of resolve, _find, _closest_frame, lookup_in_env, lookup_type, _lookup_attribute_type
