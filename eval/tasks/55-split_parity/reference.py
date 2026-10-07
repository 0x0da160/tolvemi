def solve(xs):
    return ([x for x in xs if x % 2 == 0], [x for x in xs if x % 2 != 0])
