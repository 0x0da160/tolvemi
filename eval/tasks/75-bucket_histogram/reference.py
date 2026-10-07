def solve(p):
    w, xs = p
    if not xs:
        return []
    counts = [0] * (max(xs) // w + 1)
    for v in xs:
        counts[v // w] += 1
    return counts

def gen(rng, g):
    return (rng.randint(1, 6), [rng.randint(0, 49) for _ in range(rng.randint(0, 8))])
