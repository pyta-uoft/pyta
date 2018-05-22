# Typechecking status


## Nodes
**TODOs:**
- Think of better ways of representing objects when returning error messages from typechecking.

### Assign

**TODOs:**
Done.

### BinOp

Done.

### BoolOp

Done.

### Call

**TODOs:**
* Improve handling of initializers
  * Check number of arguments when instantiating a class that uses an initializer with multiple arguments
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

**TODOs:**
- do proper type-checking of arguments

### Subscript

**TODOs:**
- Handle ExtSlice

### Tuple

Done.

### UnaryOp

Done.
