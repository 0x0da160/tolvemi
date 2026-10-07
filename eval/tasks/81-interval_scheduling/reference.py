def solve(xs):
    count, last = 0, None
    for s, e in xs:
        if last is None or s >= last:
            count += 1
            last = e
    return count

def gen(rng, g):
    ivs = []
    for _ in range(rng.randint(0, 8)):
        s = rng.randint(-5, 10)
        ivs.append((s, s + rng.randint(1, 5)))
    return sorted(ivs, key=lambda iv: (iv[1], iv[0]))
