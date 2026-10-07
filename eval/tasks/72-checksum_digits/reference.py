def solve(ds):
    if not ds:
        return False
    s = 0
    for i, d in enumerate(reversed(ds)):
        if i % 2 == 1:
            d *= 2
            if d > 9:
                d -= 9
        s += d
    return s % 10 == 0

def gen(rng, g):
    ds = [rng.randint(0, 9) for _ in range(rng.randint(0, 10))]
    if ds and rng.random() < 0.5:
        ds[-1] = 0
        ds[-1] = (10 - sum_luhn(ds) % 10) % 10
    return ds

def sum_luhn(ds):
    s = 0
    for i, d in enumerate(reversed(ds)):
        if i % 2 == 1:
            d *= 2
            if d > 9:
                d -= 9
        s += d
    return s
