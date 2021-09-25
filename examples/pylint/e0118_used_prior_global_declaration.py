TIME = 0

def timestep() -> None:
    """Increment global time by 1."""
    print(TIME)  # Error on this line
    global TIME
    TIME += 1
