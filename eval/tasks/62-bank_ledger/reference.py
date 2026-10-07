def solve(xs):
    bal, rej = 0, 0
    for x in xs:
        if bal + x >= 0:
            bal += x
        else:
            rej += 1
            if bal >= 1:
                bal -= 1
    return (bal, rej)

def gen(rng, g):
    return [rng.randint(-9, 9) for _ in range(rng.randint(0, 10))]
