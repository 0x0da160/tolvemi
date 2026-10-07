def solve(xs):
    out = []
    for x in xs:
        out.append(x if not out or out[-1] < x else out[-1])
    return out
