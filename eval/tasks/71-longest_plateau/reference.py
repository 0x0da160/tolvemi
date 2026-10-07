def solve(xs):
    best = None
    i = 0
    while i < len(xs):
        j = i
        while j < len(xs) and xs[j] == xs[i]:
            j += 1
        if best is None or j - i > best[1]:
            best = (xs[i], j - i)
        i = j
    return best

def gen(rng, g):
    return [rng.randint(0, 3) for _ in range(rng.randint(0, 12))]
