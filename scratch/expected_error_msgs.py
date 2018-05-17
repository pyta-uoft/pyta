x = 3
x = 'abc'

'''
Error: Type inference contradiction in the expression
    <line#> | x
Expected type is 'int' due to the expression
    <line#> | x = 3
but used as 'str' in
    <line#> | x = 'abc'
'''

################################################################################

def f(a, b):
    return a == b

f('abc', True)

'''
Error: Type inference contradiction in the parameter 'a' of
    <line#> | f(a, b)
Expected type is 'bool' due to the expression
    <line#> | return a == b
but passed in a 'str' in the expression
    <line#> | f('abc', True)
'''

################################################################################

x = 3
y = x

def f(a):
    return a == 0

f(y)

'''
Error: Type inference contradiction in the parameter 'a' of
    <line#> | f(a)
Expected type is 'bool' due to the expression
    <line#> | return a == 0
but passed in an 'int' in the expression
    <line#> | f(y)
    
Namely,

* type of
    <line#> | y
is 'int' due to the expression
    <line#> | y = x
* type of 
    <line#> | x
is 'int' due to the expression
    <line#> | x = 3
'''

################################################################################

x = 0

def f(a):
    return a + x

def g(b):
    return b + 'abc'

g(f(x))

'''
Error: Type inference contradiction in the parameter 'b' of
    <line#> | g(b)
Expected type is 'str' due to the expression
    <line#> | return b + 'abc'
but passed in an 'int' in the expression
    <line#> g(f(x))
    
Namely,

* type of
    <line#> | f(x) 
is 'int' due to the expression
    <line#> | return a + x
* type of
    <line#> | x
is 'int' due to the expression
    <line#> | x = 0
    
'''

################################################################################

