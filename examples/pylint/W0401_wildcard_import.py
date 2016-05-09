"""pylint: wildcard import

Only import what you need. Wildcard imports are generally bad because they
'pollute' the namespace with all the functions.

Rather than importing everything with wildcard '*', try importing specific
functions for example:
>>> from module_name import certain_definition

Or, if you need to import many functions, import them the following way, to
keep them separated in the namespace by module name:
>>> import module_name

... then you can use the function like, module_name.function_name

Or, you can create an alias for module names with:
>>> import tyrannosaurus_rex as dino

... which can be used like: dino.function_name

"""

from valid_module import *
