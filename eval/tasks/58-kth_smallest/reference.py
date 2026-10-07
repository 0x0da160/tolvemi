def solve(p):
    xs, k = p
    s = sorted(xs)
    return s[k] if 0 <= k < len(s) else None

def gen(rng, g):
    xs = [g.int(rng) for _ in range(rng.randint(0, 6))]
    return (xs, rng.randint(-1, len(xs)))
