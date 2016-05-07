# Start of the program, so we don't have any try/except surrounding the code.
if __name__ == "__main__":
    numerator = 5
    denominator = 0
    if denominator == 0:
        raise Exception('Bad denominator')
    else:
        print(numerator / denominator)

    
