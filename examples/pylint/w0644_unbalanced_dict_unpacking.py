"""Examples for W0644 unbalanced-dict-unpacking"""

SCORES = {
    "bob": (1, 1, 3, 2),
    "joe": (4, 3, 1, 2),
    "billy": (2, 2, 2, 2),
}

a, b = SCORES   # unbalanced-dict-unpacking

for d, e in SCORES.values():  # unbalanced-dict-unpacking
    print(d)
