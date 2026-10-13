def solve(inp):
    b, xs = inp
    out = []
    for n in xs:
        ds = [n % b]
        n //= b
        while n > 0:
            ds.append(n % b)
            n //= b
        out.append(ds[::-1])
    return out


def gen(rng, g):
    b = rng.choice([2, 3, 7, 8, 10, 16]) if rng.random() < 0.6 else rng.randint(2, 16)
    def num():
        r = rng.random()
        if r < 0.15:
            return rng.choice([0, 1, b - 1, b, b * b, b * b - 1])
        if r < 0.75:
            return rng.randint(0, 10000)
        return rng.randint(0, 10 ** 12)
    return [b, [num() for _ in range(rng.randint(0, 8))]]
