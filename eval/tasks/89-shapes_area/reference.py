def solve(xs):
    total, bad = 0, 0
    for name, dims in xs:
        if name == "circle" and len(dims) == 1:
            total += 3 * dims[0] * dims[0]
        elif name == "rect" and len(dims) == 2:
            total += dims[0] * dims[1]
        elif name == "square" and len(dims) == 1:
            total += dims[0] * dims[0]
        else:
            bad += 1
    return (total, bad)


def gen(rng, g):
    def one():
        if rng.random() < 0.65:
            name, n = rng.choice([("circle", 1), ("rect", 2), ("square", 1)])
        else:
            name, n = rng.choice(["circle", "rect", "square", "tri", "Circle", ""]), rng.choice([0, 1, 2, 3])
        return (name, [rng.randint(-5, 9) for _ in range(n)])

    return [one() for _ in range(rng.randint(0, 6))]
