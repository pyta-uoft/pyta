"""pylint: Using possibly loop variable %r outside the loop that is undefined.

"""

for i in range(0, 2): # i is undefined outside the loop.
    print(i)

print(i) # Using loop variable i outside the loop.
