"""pylint:  Possible unbalanced unpacking assignment with sequence%s: left side has %d
label(s), right side has %d value(s).

Note: Number of label(s) on the left side and number of value(s) on the right
side must always be the same in an unpacking assignment.
"""

def set_values(var1, var2):

    var1 = 1
    var2 = 2
    return var1, var2

var2, var4, var5 = set_values(var1, var2) # Error on this line 
