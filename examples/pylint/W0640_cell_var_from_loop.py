"""pylint: Cell variable %s defined in loop A variable used in a
closure is defined in a loop. This will result in all closures
using the same value for the closed-over variable.

"""

for i in range(5):
    def print_fun():
        print(i) # Error on this line 
