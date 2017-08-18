from typing import List

def make_list(n: int, lst: List[int]=[]) -> List[int]:
    for i in range(n):
        lst.append(i)
    return lst


print(make_list(5))
print(make_list(5))
