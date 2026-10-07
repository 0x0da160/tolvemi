def solve(xs):
    return 0 in xs

def gen(rng, g):
    return [rng.randint(-3, 3) for _ in range(rng.randint(0, 6))]
