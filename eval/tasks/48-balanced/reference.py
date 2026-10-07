def solve(xs):
    d = 0
    for x in xs:
        d += 1 if x else -1
        if d < 0:
            return False
    return d == 0

def gen(rng, g):
    n = rng.randint(0, 5)
    xs = []
    def build(k):
        out = []
        while k > 0:
            inner = rng.randint(0, k - 1)
            out += [True] + build(inner) + [False]
            k -= inner + 1
        return out
    xs = build(n)
    if xs and rng.random() < 0.5:
        i, j = rng.randrange(len(xs)), rng.randrange(len(xs))
        xs[i], xs[j] = xs[j], xs[i]
        if rng.random() < 0.3:
            xs.pop(rng.randrange(len(xs)))
    return xs
