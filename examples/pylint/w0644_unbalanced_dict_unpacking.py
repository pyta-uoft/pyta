"""Examples for W0644 unbalanced-dict-unpacking"""

SCORES = {
    "bob": (1, 1, 3, 2),
    "joe": (4, 3, 1, 2),
    "billy": (2, 2, 2, 2),
}

a, b = SCORES  # Error on this line

for d, e in SCORES.values():  # Error on this line
    print(d)
