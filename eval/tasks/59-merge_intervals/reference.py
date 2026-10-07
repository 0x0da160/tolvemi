def solve(xs):
    out = []
    for s, e in xs:
        if out and s <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], e))
        else:
            out.append((s, e))
    return out

def gen(rng, g):
    starts = sorted(rng.randint(-10, 20) for _ in range(rng.randint(0, 6)))
    return [(s, s + rng.randint(0, 6)) for s in starts]
