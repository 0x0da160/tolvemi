def solve(rows):
    if not rows:
        return []
    return [[r[j] for r in rows] for j in range(len(rows[0]))]

def gen(rng, g):
    m, n = rng.randint(0, 4), rng.randint(0, 4)
    return [[g.int(rng) for _ in range(n)] for _ in range(m)]
