if 5:
    print("5 is a constant")
elif 4 and 3:
    print("4 and 3 are constants")

x = 100
if x or 1:
    print("x is not a constant but 1 is")

if not (x and (x or 1)):
    print("there is still a constant 1")

if (x and (x and (x and (x and (x and (x and 1)))))):
    print("there is still a constant 1")
