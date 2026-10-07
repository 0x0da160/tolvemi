def solve(p):
    t, xs = p
    for j in range(len(xs)):
        for i in range(j):
            if xs[i] + xs[j] == t:
                return (i, j)
    return None

def gen(rng, g):
    return (rng.randint(-4, 10), [rng.randint(-3, 6) for _ in range(rng.randint(0, 8))])
