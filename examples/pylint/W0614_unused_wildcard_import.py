"""pylint: imported module or variable %s is not used from a ‘from X import *’ style import.

"""

from logging import * # Error on this line

def fun():
    print("logging unused.")
    
fun() 
