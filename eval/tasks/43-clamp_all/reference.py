def solve(p):
    (lo, hi), xs = p
    return [min(max(x, lo), hi) for x in xs]

def gen(rng, g):
    a, b = sorted((g.int(rng), g.int(rng)))
    return ((a, b), [g.int(rng) for _ in range(rng.randint(0, 7))])
