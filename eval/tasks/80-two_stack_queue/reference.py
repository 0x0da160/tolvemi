def solve(ops):
    q, out = [], []
    for op in ops:
        if op >= 0:
            q.append(op)
        elif q:
            out.append(q.pop(0))
    return out

def gen(rng, g):
    return [-1 if rng.random() < 0.4 else rng.randint(0, 9) for _ in range(rng.randint(0, 12))]
