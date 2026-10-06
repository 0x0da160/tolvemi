def solve(xs):
    out = []
    for x in xs:
        if x not in out:
            out.append(x)
    return out

def gen(rng, g):
    return [rng.randint(-2, 2) for _ in range(rng.randint(0, 9))]
