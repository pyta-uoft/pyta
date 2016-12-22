# TODOs for node documentation

## Assign

The type of `targets` can probably be more specific to just a small
set of node classes (e.g., `Name`?).

It would be good to show different examples of the different nodes that could appear on the left,
as well as an example of multiple assignment:

```python
x = y = z = 1 + 2
```

## AsyncFor

Example for `orelse` is wrong (the `else` is currently tied to the `if` rather than the `for` loop.

## AsyncFunctionDef

The example does not use the `async` keyword, and so does not actually illustrate an `AsyncFunctionDef`.

## Attribute

The descriptions for both the node itself and both of its attributes need work.


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

## Import

Not all imports need to have an alias (e.g., `import astroid` vs. `import astroid as ast`).
It would be good to show an example of both, and how the attribute values differ.

Also would be good to show having multiple imports on the same line.

## ImportFrom

Same comment as `Import`. Also worth investigating: is the `level` attribute on `Import` as well?

## Index

The type of `value` is more general; e.g., `x[1+2]`.

## ListComp

It seems like the type of `Generators` should be `List[Comprehension]`,
unless there is another possibility for these elements?

## Nonlocal

The example is technically incorrect, and is a little misleading.
`nonlocal` can only be used to refer to variables in some outer scope that is *not* the global scope (apparently).

So the example should be changed to something like

```python
def outer():
    x = 10
    y = 100
    def inner(y):
        nonlocal x, y
        x = 3 * y
    inner(1)
    return x
```

## Return

The type of `value` should be `Expr | None`.

In Example 1's documentation, the value of `value` should be explicitly written as `None`.

## Set

Description of `elts` should refer to "this set" rather than "this list."

## Slice

The types of the three attributes should be arbitrary `Expr` nodes, but you can say that they must evaluate to an integer for the expression to be successful at runtime.

Also if they can be None, use `Expr | None`.

## Starred

Would be good to mention what the `Starred` node appears under in the example, since it's not immediately obvious. (Is there an implicit `Tuple` representing the assignment targets?)

## TryExcept

Explicitly write `None` for the value that is None in the example.

Would be good to give an example of how to get a non-None value for `orelse`, presumably using `else`.

## TryFinally

It seems like the `body` actually has type `TryExcept`.

## While

The `test` can be an arbitrary `Expr` (e.g., imagine a function call here).

In the example, the `test` is actually a `Const` node with value `True`.

## With

It seems like `items` is a list of tuples, not a list of `Expr`.

## Yield

Express the type of `value` as `Expr | None`.

Explicitly write `None` in the first example description.

## YieldFrom

The type of `value` is not necessarily a `GeneratorExp` (in fact, in the example given it is a `Call`).
