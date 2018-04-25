# Typechecking status


## Nodes

### Assign

TODOs:
    - Check for unpacking tuple assignment where the LHS and RHS have different lengths.

### BinOp

Done.

### BoolOp

Done.

### Call

TODOs:
    - Handling of "overloaded" functions (with optional arguments)
    - Improve handling of initializers
    - Handling inheritance

### Compare

Done.

### Const
Done.

## Dict

TODOs: see List.

### List

TODOs:
    - Represent the type of an empty list.
    - Flag to require homogeneity (?)
    - Lists in assignment ("Store") context
    - Better articulate Any vs. Object

### Name

TODOs:
    - unify lookup approaches for builtins vs. user-defined variables.

### Set

TODOs: see List.


### Tuple

Done.

### UnaryOp

Done.
