def solve(xs):
    return all(a <= b for a, b in zip(xs, xs[1:]))

def gen(rng, g):
    xs = sorted(g.int(rng) for _ in range(rng.randint(0, 7)))
    if len(xs) > 1 and rng.random() < 0.5:
        rng.shuffle(xs)
    return xs
