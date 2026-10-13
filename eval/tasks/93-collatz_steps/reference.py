def solve(xs):
    out = []
    for n in xs:
        steps = 0
        while n != 1 and steps <= 100:
            n = n // 2 if n % 2 == 0 else 3 * n + 1
            steps += 1
        out.append(steps if n == 1 and steps <= 100 else -1)
    return out


def gen(rng, g):
    special = [1, 2, 3, 6, 7, 27, 97, 107, 214, 322, 644, 871, 1000]
    return [rng.choice(special) if rng.random() < 0.3 else rng.randint(1, 1000) for _ in range(rng.randint(0, 8))]
