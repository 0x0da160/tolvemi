def solve(p):
    v, xs = p
    return xs.count(v)

def gen(rng, g):
    xs = [rng.randint(-3, 3) for _ in range(rng.randint(0, 8))]
    return (rng.randint(-3, 3), xs)
