def solve(ops):
    inv = {}
    for item, change in ops:
        q = inv.get(item, 0) + change
        if q == 0:
            inv.pop(item, None)
        else:
            inv[item] = q
    return [(k, v) for k, v in inv.items()]


ITEMS = ["apple", "pear", "fig", "kiwi", "plum", "lime", "date", "melon", "grape", "cherry"]


def gen(rng, g):
    items = rng.sample(ITEMS, rng.randint(1, len(ITEMS)))
    n = rng.choice([0, 1, 3, 8, 15, 30, 60]) if rng.random() < 0.8 else rng.randint(100, 200)
    ops = []
    for _ in range(n):
        r = rng.random()
        if r < 0.2:
            change = rng.choice([-3, -2, -1, 1, 2, 3])
        elif r < 0.9:
            change = rng.randint(-2, 2)
        else:
            change = rng.randint(-1000, 1000)
        ops.append([rng.choice(items), change])
    return ops
