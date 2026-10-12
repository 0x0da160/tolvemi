def solve(s):
    return len(s.split())


def gen(rng, g):
    return "".join(rng.choice("ab  x,9") for _ in range(rng.randint(0, 16)))
