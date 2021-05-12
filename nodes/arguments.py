"""
Arguments astroid node

The arguments for a function.

Attributes:
    - annotations                 (List[NodeNG]])
        - The type annotations of arguments that can be passed positionally.
    - args                       (List[NodeNG])
        - A list of non-keyword argument names. If None, args is an empty list.
    - defaults                  (List[NodeNG])
        - A list of default values for arguments that can be passed
          positionally. If None, defaults is an empty list.
    - kw_defaults               (List[NodeNG])
        - A list of default values for keyword-only arguments. If None,
          kw_defaults is an empty list.
    - kwarg                     (str)
        - The name of the variable length keyword arguments.
    - kwargannotation           (NodeNG)
        - The type annotation for the variable length keyword arguments.
    - kwonlyargs                (List[AssignName])
        - A list of keyword-only argument names. If None, kwonlyargs is an empty
          list.
    - kwonlyargs_annotations    (List[NodeNG])
        - The type annotations of arguments that cannot be passed positionally.
    - posonlyargs               (List[AssignName])
        - The arguments that can only be passed positionally.
    - posonlyargs_annotations   (List[NodeNG])
        - The type annotations of arguments that can only be passed positionally.
    - type_comment_args         (List[NodeNG])
        - The type annotation, passed by a type comment, of each argument. None if not specified.
    - type_comment_kwonlyargs   (List[NodeNG])
        - The type annotation, passed by a type comment, of each keyword only argument. None if
        not specified.
    - type_comment_posonlyargs  (List[NodeNG])
        - The type annotation, passed by a type comment, of each positional argument. None if not
        specified.
    - vararg                    (str)
        - A variable-length argument's name.
    - varargannotation          (NodeNG)
        - The type annotation for the variable length arguments.

Example:
    - Arguments(
               vararg='d',
               kwarg='g',
               args=[
                  AssignName(name='a'),
                  AssignName(name='b'),
                  AssignName(name='c')],
               defaults=[Const(value=1), Const(value=2)],
               kwonlyargs=[AssignName(name='e'), AssignName(name='f')],
               posonlyargs=[],
               posonlyargs_annotations=[],
               kw_defaults=[None, Const(value=3)],
               annotations=[
                  Const(value='annotation'),
                  None,
                  None],
               varargannotation=None,
               kwargannotation=None,
               kwonlyargs_annotations=[None, None],
               type_comment_args=[
                  None,
                  None,
                  None],
               type_comment_kwonlyargs=[None, None],
               type_comment_posonlyargs=[])

"""


def f(a: 'annotation', b=1, c=2, *d, e, f=3, **g):
    pass
