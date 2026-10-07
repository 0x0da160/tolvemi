def solve(xs):
    total = 0
    for i, x in enumerate(xs):
        if i + 1 < len(xs) and x < xs[i + 1]:
            total -= x
        else:
            total += x
    return total

_TABLE = [(1000, [1000]), (900, [100, 1000]), (500, [500]), (400, [100, 500]), (100, [100]), (90, [10, 100]),
          (50, [50]), (40, [10, 50]), (10, [10]), (9, [1, 10]), (5, [5]), (4, [1, 5]), (1, [1])]

def gen(rng, g):
    n = rng.choice([rng.randint(1, 50), rng.randint(1, 500), rng.randint(1, 3999)])
    out = []
    for v, syms in _TABLE:
        while n >= v:
            out += syms
            n -= v
    return out
