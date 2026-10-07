def solve(p):
    k, xs = p
    return [max(xs[i:i + k]) for i in range(len(xs) - k + 1)]

def gen(rng, g):
    return (rng.randint(1, 4), [rng.randint(-5, 9) for _ in range(rng.randint(0, 9))])
