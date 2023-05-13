"""Examples for W3601 bad-chained-comparison"""

x = 5

if 0 < x is 5:  # bad-chained-comparison
    print("hi")

a = 1
lis = [1, 2, 3, 4]

if a > 0 not in lis:  # bad-chained-comparison
    print("whee")

if a == x is 1 in lis:  # bad-chained-comparison
    print("yikes")
