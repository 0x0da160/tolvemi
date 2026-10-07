def solve(xs):
    out, s = [], 0
    for x in xs:
        s += x
        out.append(s)
    return out
