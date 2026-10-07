def solve(p):
    v, xs = p
    return xs.index(v) if v in xs else None

def gen(rng, g):
    return (rng.randint(-3, 3), [rng.randint(-3, 3) for _ in range(rng.randint(0, 7))])
