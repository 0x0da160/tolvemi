def solve(tokens):
    def ev(i):
        t = tokens[i]
        if t not in ("+", "-", "*"):
            return int(t), i + 1
        a, i = ev(i + 1)
        b, i = ev(i)
        return (a + b if t == "+" else a - b if t == "-" else a * b), i

    return ev(0)[0]


def gen(rng, g):
    def expr(depth):
        if depth == 0 or rng.random() < 0.3:
            return [str(rng.choice([0, 1, 2, 7, 10, 99, rng.randint(0, 999)]))]
        return [rng.choice("+-*")] + expr(depth - 1) + expr(depth - 1)

    return expr(rng.randint(0, 5))
