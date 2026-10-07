def solve(xs):
    return sum(x if i % 2 == 0 else -x for i, x in enumerate(xs))
