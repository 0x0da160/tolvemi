def solve(prog):
    st = []
    for tag, v in prog:
        if tag == 0:
            st.append(v)
        else:
            if len(st) < 2:
                return None
            b = st.pop()
            a = st.pop()
            st.append(a + b if tag == 1 else a - b if tag == 2 else a * b)
    return st[0] if len(st) == 1 else None

def gen(rng, g):
    if rng.random() < 0.2:
        return [(rng.randint(0, 3), rng.randint(-5, 9)) for _ in range(rng.randint(0, 6))]
    prog, depth = [], 0
    for _ in range(rng.randint(1, 8)):
        if depth < 2 or rng.random() < 0.5:
            prog.append((0, rng.randint(-5, 9)))
            depth += 1
        else:
            prog.append((rng.randint(1, 3), rng.randint(0, 3)))
            depth -= 1
    while depth > 1 and rng.random() < 0.8:
        prog.append((rng.randint(1, 3), 0))
        depth -= 1
    return prog
