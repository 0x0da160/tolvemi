def solve(xs):
    out = []
    for x in xs:
        if x not in out:
            out.append(x)
    return out

def gen(rng, g):
    return [rng.randint(-3, 3) for _ in range(rng.randint(0, 8))]
