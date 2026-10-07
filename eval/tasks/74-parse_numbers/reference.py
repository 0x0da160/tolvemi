def solve(ds):
    out = []
    cur = None
    for d in ds:
        if d < 0:
            if cur is not None:
                out.append(cur)
            cur = None
        else:
            cur = (cur or 0) * 10 + d
    if cur is not None:
        out.append(cur)
    return out

def gen(rng, g):
    return [-1 if rng.random() < 0.3 else rng.randint(0, 9) for _ in range(rng.randint(0, 12))]
