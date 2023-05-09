"""Examples for W0644 unbalanced-dict-unpacking"""

SCORES = {
    "bob": (1, 1, 3, 2),
    "joe": (4, 3, 1, 2),
    "billy": (2, 2, 2, 2),
}

c, d = SCORES   # unbalanced-dict-unpacking

for a, b in SCORES.values():  # unbalanced-dict-unpacking
    print(a)
