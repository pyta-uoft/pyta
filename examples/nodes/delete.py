"""
Delete astroid node

Delete node represents a del statement.

Attributes:
    - targets   (list[DelName | DelAttr | Subscript | assignable])
        - The targets to be deleted. These must have a Del expression context,
          such as DelName and DelAttr themselves, or any assignable node
          except AssignName and AssignAttr. (See the README for more details.)

Example 1:
    Delete(targets=[DelName(name='x')])

Example 2:
    Delete(targets=[
        DelName(name='x'),
        DelAttr(
            attrname='attr',
            expr=Name(name='self')),
        Subscript(
            ctx=<Context.Del: 3>,
            value=Name(name='y'),
            slice=Const(value=0))])
"""

# Example 1
del x

# Example 2
del x, self.attr, y[0]
