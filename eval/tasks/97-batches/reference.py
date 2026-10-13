def solve(inp):
    k, rs = inp
    return [([n for n, _ in rs[i:i + k]], sum(a for _, a in rs[i:i + k])) for i in range(0, len(rs), k)]


NAMES = ["ann", "bob", "cy", "dee", "eve", "fay", "gus", "hal", "ivy", "jo"]


def gen(rng, g):
    k = rng.randint(1, 5)
    n = rng.choice([0, 1, 2, 4, 7, 12, 25]) if rng.random() < 0.8 else rng.randint(50, 120)
    rs = []
    for _ in range(n):
        amount = rng.randint(-50, 50) if rng.random() < 0.9 else rng.randint(-100000, 100000)
        rs.append([rng.choice(NAMES), amount])
    return [k, rs]
