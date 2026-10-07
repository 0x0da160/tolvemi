def solve(xs):
    best = 0
    for i in range(len(xs)):
        seen = set()
        for j in range(i, len(xs)):
            seen.add(xs[j])
            if len(seen) > 2:
                break
            best = max(best, j - i + 1)
    return best

def gen(rng, g):
    return [rng.randint(0, 3) for _ in range(rng.randint(0, 12))]
