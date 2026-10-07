def solve(xs):
    stack = []
    for c in xs:
        if c > 0:
            stack.append(c)
        elif not stack or stack.pop() != -c:
            return False
    return not stack

def gen(rng, g):
    out, stack = [], []
    for _ in range(rng.randint(0, 10)):
        if stack and rng.random() < 0.45:
            out.append(-stack.pop())
        else:
            k = rng.randint(1, 3)
            stack.append(k)
            out.append(k)
    if rng.random() < 0.6:
        out.extend(-k for k in reversed(stack))
    if out and rng.random() < 0.35:
        i = rng.randrange(len(out))
        out[i] = rng.choice([v for v in (1, 2, 3, -1, -2, -3) if v != out[i]])
    return out
