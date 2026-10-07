def solve(xs):
    if not xs:
        return None
    return (min(xs), (max(xs), sum(xs)))

def gen(rng, g):
    return [g.int(rng) for _ in range(rng.randint(0, 8))]
