def solve(xs):
    d, mx, first = 0, 0, -1
    for i, s in enumerate(xs):
        d += s
        mx = max(mx, d)
        if d < 0 and first == -1:
            first = i
    return (mx, first)

def gen(rng, g):
    return [1 if rng.random() < 0.55 else -1 for _ in range(rng.randint(0, 10))]
