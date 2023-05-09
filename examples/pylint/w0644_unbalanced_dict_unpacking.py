"""Examples for W0644 unbalanced-dict-unpacking"""

SCORES = {
    "bob": (1, 1, 3, 2),
    "joe": (4, 3, 1, 2),
    "billy": (2, 2, 2, 2),
}

for a, b, c, d in SCORES.values():  # unbalanced-dict-unpacking
    print(a)
