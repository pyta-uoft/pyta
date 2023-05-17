"""Examples for W3601 bad-chained-comparison"""

x = 5

if 0 < x is 5:  # Error on this line
    print("hi")

a = 1
my_list = [1, 2, 3, 4]

if a > 0 not in my_list:  # Error on this line
    print("whee")

if a == x is 1 in my_list:  # Error on this line
    print("yikes")
