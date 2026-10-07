def solve(rolls):
    score, i = 0, 0
    for _ in range(10):
        if rolls[i] == 10:
            score += 10 + rolls[i + 1] + rolls[i + 2]
            i += 1
        elif rolls[i] + rolls[i + 1] == 10:
            score += 10 + rolls[i + 2]
            i += 2
        else:
            score += rolls[i] + rolls[i + 1]
            i += 2
    return score

def _first(rng):
    r = rng.random()
    return 10 if r < 0.3 else rng.randint(0, 9)

def gen(rng, g):
    rolls = []
    for _ in range(9):
        a = _first(rng)
        rolls.append(a)
        if a < 10:
            rolls.append(10 - a if rng.random() < 0.35 else rng.randint(0, 10 - a))
    a = _first(rng)
    if a == 10:
        b = _first(rng)
        c = (_first(rng) if b == 10 else rng.randint(0, 10 - b))
        rolls += [a, b, c]
    else:
        b = 10 - a if rng.random() < 0.35 else rng.randint(0, 10 - a)
        rolls += [a, b] + ([_first(rng)] if a + b == 10 else [])
    return rolls
