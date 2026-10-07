def solve(ops):
    st = [0] * 5
    c = 0
    for i, d in ops:
        v = st[i] + d
        if v < 0:
            v = 0
            c += 1
        st[i] = v
    return (st, c)

def gen(rng, g):
    return [(rng.randint(0, 4), rng.randint(-5, 6)) for _ in range(rng.randint(0, 10))]
