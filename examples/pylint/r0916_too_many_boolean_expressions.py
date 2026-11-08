def check_password(password: str) -> None:
    """Print whether password is valid."""
    if (
        len(password) >= 8
        and any(character.islower() for character in password)
        and any(character.isupper() for character in password)
        and any(character.isdigit() for character in password)
        and any(character in "!@#$" for character in password)
        and " " not in password
    ):
        print("Valid password.")
    else:
        print("Invalid password.")
