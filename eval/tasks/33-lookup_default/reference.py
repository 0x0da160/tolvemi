def solve(p):
    k, entries = p
    for key, value in entries:
        if key == k:
            return value
    return 0

def gen(rng, g):
    entries = [(rng.randint(0, 4), g.int(rng)) for _ in range(rng.randint(0, 6))]
    return (rng.randint(0, 4), entries)
