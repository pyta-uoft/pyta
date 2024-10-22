from __future__ import annotations

def make_list(n: int, lst: list[int]=[]) -> list[int]:
    for i in range(n):
        lst.append(i)
    return lst


print(make_list(5))
print(make_list(5))
