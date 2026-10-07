def solve(xs):
    best = None
    for i in range(len(xs)):
        s = 0
        for j in range(i, len(xs)):
            s += xs[j]
            if best is None or s > best[0]:
                best = (s, (i, j))
    return best

def gen(rng, g):
    return [rng.randint(-6, 6) for _ in range(rng.randint(0, 9))]
