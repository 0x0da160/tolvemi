def solve(xs):
    best = cur = 0
    for x in xs:
        cur = max(0, cur + x)
        best = max(best, cur)
    return best
