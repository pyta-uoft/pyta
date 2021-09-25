students_info = [[1002123, "Alex H", "CS"], [1001115, "Jack K", "PSY"]]

cs_student_dict = dict()  # Error on this line.

for student in students_info:
    if student[2] == "CS":
        cs_student_dict[student[0]] = student[1]
