class NoSelfUsage:
    def __init__(self):
        self.a = 42

    def no_self(self, num):
        num = num + 2
        print(num)

# You would fix it as follows by moving it outside the class:
def no_self(num):
    num = num + 2
    print(num)
