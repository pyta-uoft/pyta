"""pylint: Using possibly undefined loop variable %r.

"""
for i in range(5):
    print(i)

for i in range(5): # Error on this line
    print(i) 
