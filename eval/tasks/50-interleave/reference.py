def solve(p):
    xs, ys = p
    out = []
    for i in range(max(len(xs), len(ys))):
        if i < len(xs):
            out.append(xs[i])
        if i < len(ys):
            out.append(ys[i])
    return out
