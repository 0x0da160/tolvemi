def solve(p):
    xs, k = p
    return [sum(xs[i:i + k]) for i in range(len(xs) - k + 1)]

def gen(rng, g):
    return ([g.int(rng) for _ in range(rng.randint(0, 7))], rng.randint(1, 4))
