def solve(xs):
    n = len(xs)
    return [(xs[i - 1] if i > 0 else False) != (xs[i + 1] if i < n - 1 else False) for i in range(n)]

def gen(rng, g):
    return [rng.random() < 0.5 for _ in range(rng.randint(0, 10))]
