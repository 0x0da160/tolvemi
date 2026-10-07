def solve(p):
    k, xs = p
    return [x for x in xs if x % k == 0]

def gen(rng, g):
    return (rng.randint(1, 6), [g.int(rng) for _ in range(rng.randint(0, 8))])
