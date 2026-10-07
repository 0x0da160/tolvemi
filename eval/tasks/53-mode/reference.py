def solve(xs):
    if not xs:
        return None
    return min(xs, key=lambda v: (-xs.count(v), v))

def gen(rng, g):
    return [rng.randint(-3, 3) for _ in range(rng.randint(0, 8))]
