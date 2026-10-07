def solve(xs):
    return all(x > 0 for x in xs)

def gen(rng, g):
    xs = [rng.randint(1, 20) for _ in range(rng.randint(0, 6))]
    if xs and rng.random() < 0.5:
        xs[rng.randrange(len(xs))] = rng.randint(-5, 0)
    return xs
