def solve(xs):
    best = cur = 0
    prev = None
    for x in xs:
        cur = cur + 1 if prev is not None and prev < x else 1
        best = max(best, cur)
        prev = x
    return best
