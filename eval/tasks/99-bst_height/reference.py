def solve(xs):
    # a tree is None (empty) or a triple (left, value, right)
    def insert(t, x):
        if t is None:
            return (None, x, None)
        left, v, right = t
        if x < v:
            return (insert(left, x), v, right)
        if v < x:
            return (left, v, insert(right, x))
        return t

    def height(t):
        if t is None:
            return 0
        left, _, right = t
        return 1 + max(height(left), height(right))

    t = None
    for x in xs:
        t = insert(t, x)
    return height(t)


def gen(rng, g):
    n = rng.choice([0, 1, 2, 3, 5, 8, 12]) if rng.random() < 0.8 else rng.randint(20, 60)
    return [rng.randint(-20, 20) for _ in range(n)]
