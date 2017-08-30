from typing import List

def add_fruit(fruit_basket: List[str], fruit: str) -> None:
    """Add fruit to fruit_basket."""
    fruit_basket.append(fruit)
    return None

basket = ['apple', 'apple', 'orange']
new_basket = add_fruit(basket, 'banana')  # Error on this line
print(new_basket)  # Prints `None`
