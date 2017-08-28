def print_address(recipient_name: str,
        street_number_and_name: str,  # Error on this line: Wrong indentation
        city: str,  # Error on this line: Wrong indentation
        province: str,  # Error on this line: Wrong indentation
        country: str) -> None:  # Error on this line: Wrong indentation
    """Print the provided address in a standardized format."""
    address_string = (
        "{recipient_name}\n{street_number_and_name}\n{city}, {province}\n{country}".
        format(
            recipient_name=recipient_name,
            street_number_and_name=street_number_and_name,
                city=city,  # Error on this line: Wrong indentation
                province=province,  # Error on this line: Wrong indentation
                country=country))  # Error on this line: Wrong indentation
    print(address_string)
