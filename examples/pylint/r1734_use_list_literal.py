lst = [1, 2, 3, 4]
even_lst = list()  # Error on this line.

for x in lst:
    if x % 2 == 0:
        even_lst.append(x)
