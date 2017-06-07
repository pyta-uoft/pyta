def add_fruit(fruit_basket, fruit):
    fruit_basket.append(fruit)
    return None


def main():
    fruit_basket = ['apple', 'apple', 'orange']
    new_fruit_basket = add_fruit(fruit_basket, 'banana')  # Error on this line
    print(new_fruit_basket)  # prints `None`
