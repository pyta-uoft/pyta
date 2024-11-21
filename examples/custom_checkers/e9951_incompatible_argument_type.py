def calculate_area(radius: float) -> float:
    """Calculate the area of a circle with the given radius"""
    return 3.14159 * radius * radius

area = calculate_area("five") # Error: Function argument should be float, but got str

def convert_to_upper(text: str) -> str:
    """Convert the given text to uppercase"""
    return text.upper()

result = convert_to_upper(5) # Error: Function argument should be str, but got int
