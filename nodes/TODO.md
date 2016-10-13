# TODOs for node documentation

## Decorators

The description of wrapper "turns from a FunctionDef to a Decorators node" is incorrect.
A Decorators node is actually a child of a FunctionDef.

The type of the `nodes` attribute seems to be a list of names, and is certainly not type `Decorators` (this would be oddly recursive).

## DelAttr

The description is describing the behaviour of the built-in `delattr` function,
which is not the same as the `DelAttr` node.
Note that the `DelAttr` node in the file's example is *only* the code `self.attr`
in `del self.attr`.

The given example value for `expr` is incorrect.

## DelName

The description of `name` is awkwardly worded. Perhaps it's missing a word or two?

## Delete

The type of `targets` is incorrect - it should really be referring to `DelAttr` and `DelName` here.

There should be an example where the length of `targets` is greater than one.

## Dict

Type of `items` should specify that there are two nodes in each tuple:
`List[Tuple[Node, Node]]`.

## For

Don't write `Node(Name | Tuple | List)` -- this syntax doesn't mean anything.
Probably should just be `Name | Tuple | List`, but there should be different
examples illustrating the different possibilities.

Example for `iter` is incorrect - it's only the value being iterated over,
which is `range(3)` in this case.

There should be an example for `orelse` as well.

## FunctionDef

`decorators` is a list of decorators (could be more than one).

`returns` is a return annotation in the function header, not the `return` statement.
See <https://www.python.org/dev/peps/pep-3107/#return-values>

## If

Attribute should probably be `body` (not capitalized).

## IfExpr

Attribute should probably be `body` (not capitalized).

## Import

Not all imports need to have an alias (e.g., `import astroid` vs. `import astroid as ast`).
It would be good to show an example of both, and how the attribute values differ.

Also would be good to show having multiple imports on the same line.

## ImportFrom

Same comment as `Import`. Also worth investigating: is the `level` attribute on `Import` as well?

## Index

The type of `value` is more general; e.g., `x[1+2]`.

## Lambda

`args` is an `Arguments` node.


