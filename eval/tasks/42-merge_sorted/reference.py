def solve(p):
    xs, ys = p
    return sorted(xs + ys)

def gen(rng, g):
    return (sorted(g.int(rng) for _ in range(rng.randint(0, 6))), sorted(g.int(rng) for _ in range(rng.randint(0, 6))))
