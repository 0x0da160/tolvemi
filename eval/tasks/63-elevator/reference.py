def solve(fs):
    cur, dist, last, ch = 0, 0, 0, 0
    for f in fs:
        d = 1 if f > cur else -1 if f < cur else 0
        if d != 0:
            if last != 0 and d != last:
                ch += 1
            last = d
            dist += abs(f - cur)
            cur = f
    return (dist, ch)

def gen(rng, g):
    return [rng.randint(-3, 9) for _ in range(rng.randint(0, 8))]
