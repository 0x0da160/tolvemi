def solve(xs):
    s = sorted(set(xs))
    return s[-2] if len(s) >= 2 else None

def gen(rng, g):
    return [rng.randint(-4, 4) for _ in range(rng.randint(0, 6))]
