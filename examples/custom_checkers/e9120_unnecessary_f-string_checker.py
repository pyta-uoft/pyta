x = "hello"
message = f"{x}"  # error on this line

new_message = f"{x=  }"  # no error

final_message = f"{x + " world"}"  # no error

