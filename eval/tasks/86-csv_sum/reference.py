def solve(s):
    return sum(int(x) for x in s.split(","))


def gen(rng, g):
    n = rng.randint(1, 8)
    return ",".join(str(rng.choice([rng.randint(-30, 30), rng.randint(-10**9, 10**9)])) for _ in range(n))
