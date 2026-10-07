def solve(cs):
    x = y = 0
    d = 0  # 0 north, 1 west, 2 south, 3 east
    dx = [0, -1, 0, 1]
    dy = [1, 0, -1, 0]
    back = 0
    for c in cs:
        if c == 0:
            x += dx[d]
            y += dy[d]
        elif c == 1:
            d = (d + 1) % 4
        else:
            d = (d + 3) % 4
        if x == 0 and y == 0:
            back += 1
    return ((x, y), back)

def gen(rng, g):
    return [rng.choice([0, 0, 0, 1, 1, 2]) for _ in range(rng.randint(0, 14))]
