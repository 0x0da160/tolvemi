def solve(xs):
    return [name for name, score in sorted((p for p in xs if p[1] >= 50), key=lambda p: -p[1])]


def gen(rng, g):
    names = ["ann", "bob", "cy", "dee", "eve", "fay", "gus", "Al", "", "zoe"]
    return [(rng.choice(names), rng.choice([0, 30, 49, 50, 51, 72, 72, 90, 100, rng.randint(-5, 120)])) for _ in range(rng.randint(0, 8))]
