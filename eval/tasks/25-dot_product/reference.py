def solve(p):
    xs, ys = p
    return sum(a * b for a, b in zip(xs, ys))

def gen(rng, g):
    n = rng.randint(0, 6)
    return ([g.int(rng) for _ in range(n)], [g.int(rng) for _ in range(n)])
