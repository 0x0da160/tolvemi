def solve(p):
    cs, x = p
    v = 0
    for c in cs:
        v = v * x + c
    return v

def gen(rng, g):
    return ([rng.randint(-9, 9) for _ in range(rng.randint(0, 5))], rng.randint(-5, 5))
