def solve(p):
    n, xs = p
    return xs[:n]

def gen(rng, g):
    return (rng.randint(0, 8), [g.int(rng) for _ in range(rng.randint(0, 6))])
