# TODOs for node documentation

## AugAssign

Like `Assign`, would be good to show an example of augmented assignment with multiple targets.
(Didn't even know this is possible.)

## BinOp

Investigate whether the `op` attribute for `BinOp` can really be any node,
or only certain classes.
For example, there's no `Add` astroid node, so what is really stored?

## BoolOp

Same question as `BinOp` about the `op` attribute.

Also, it seems like there should be more investigation into `values`.
If this is a list, does that mean `BoolOp` doesn't just represent binary operations?
We should give an example for other cases then.

## Compare

Same general question as `BinOp` and `BoolOp` about what is actually being stored in `ops`.

Would also be good to have a chained comparison expression like `3 < 4 < 5` documented.

## Comprehension

Should specifically reference other astroid nodes that use `Comprehension`, e.g. `ListComp`.

Should give an example of using an `if`; also, the example seems to contradict the statement that `ifs` is None (rather than an empty list) if there are no `if`s.

Finally, the variable name given in the example documentation is incorrect.

## Const

The description of `value` should really reference the fact that these are literal constants rather than just computed values.
