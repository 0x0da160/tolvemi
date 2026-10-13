def solve(inp):
    ws, ns = inp
    def adj(xs):
        return [(xs[i], xs[i + 1]) for i in range(len(xs) - 1)]
    return (adj(ws), adj(ns))


NAMES = ["ann", "bob", "cy", "dee", "eve", "fay", "gus", "hal", "ivy", "jo"]


def gen(rng, g):
    nw = rng.choice([0, 1, 2, 3, 5, 8]) if rng.random() < 0.8 else rng.randint(20, 40)
    ni = rng.choice([0, 1, 2, 4, 7, 12]) if rng.random() < 0.8 else rng.randint(20, 40)
    ws = [rng.choice(NAMES) for _ in range(nw)]
    ns = [rng.randint(-50, 50) if rng.random() < 0.9 else rng.randint(-100000, 100000) for _ in range(ni)]
    return [ws, ns]
