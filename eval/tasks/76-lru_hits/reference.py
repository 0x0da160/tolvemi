def solve(p):
    cap, reqs = p
    cache = []  # most recently used last
    hits = 0
    for r in reqs:
        if r in cache:
            hits += 1
            cache.remove(r)
        cache.append(r)
        if len(cache) > cap:
            cache.pop(0)
    return hits

def gen(rng, g):
    return (rng.randint(1, 4), [rng.randint(0, 5) for _ in range(rng.randint(0, 14))])
