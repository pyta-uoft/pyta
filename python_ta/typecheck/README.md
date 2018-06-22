# Typechecking status


## Nodes

### Assign

Done.

### Attribute

**TODOs:**
- Handle class and static methods.

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

Done

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

Done.

### Tuple

Done.

### UnaryOp

Done.


## Type Inference

### Conversion to Monadic Functions

Done. `lookup_type()` and `types_in_callable()` remain, but should be used purely for testing purposes

### TODOs
- Remove duplicated functionality between unify, _unify_generic and unify_call
- Remove duplicated functionality between unify_call and _handle_call
- Unify functionality of resolve, find_parent, _closest_frame, lookup_in_env, lookup_type, _lookup_attribute_type
- Update _handle_call to reflect changes to _TNode structure, particularly when looking up methods with multiple type signatures
- Support for type inference with inheritance 
