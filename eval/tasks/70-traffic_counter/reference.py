def solve(ev):
    green, passed, wait = False, 0, 0
    for e in ev:
        if e == 0:
            if green and wait == 0:
                passed += 1
            else:
                wait += 1
        elif e == 1:
            if not green:
                green = True
                k = min(3, wait)
                passed += k
                wait -= k
        else:
            green = False
    return (passed, wait)

def gen(rng, g):
    return [rng.choices([0, 1, 2], weights=[6, 3, 2])[0] for _ in range(rng.randint(0, 12))]
