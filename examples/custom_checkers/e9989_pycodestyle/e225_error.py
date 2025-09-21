x = 5
if x>5:  # missing whitespace around single character operator
    print("x > 5")

if x==5:  # missing whitespace around multiple character operator
    print("x == 5")

if x>=5 or x<=5 or x!=5:  # missing whitespace around multicharacter operators
    print("x >= 5 or x <= 5 or x != 5")

(x:=10)  # missing whitespace around multicharacter operator

x+=7  # missing whitespace around multicharacter operator

x>>=7  # missing whitespace around multicharacter operator

x<<=7  # missing whitespace around multicharacter operator

x**=8  # missing whitespace around multicharacter operator
