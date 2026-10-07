def solve(xs):
    return sum(1 for a, b in zip(xs, xs[1:]) if b > a)
