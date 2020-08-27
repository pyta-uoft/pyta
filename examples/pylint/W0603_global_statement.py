my_list = [1,2,3]

def f() -> None:
    global my_list  # Error on this line
    my_list.append(4)
