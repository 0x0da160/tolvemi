def solve(xs):
    out = []
    for x in xs:
        if out and out[-1][0] == x:
            out[-1] = (x, out[-1][1] + 1)
        else:
            out.append((x, 1))
    return out

def gen(rng, g):
    return [rng.randint(0, 2) for _ in range(rng.randint(0, 9))]
