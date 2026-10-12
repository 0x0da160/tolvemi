def solve(p):
    args, text = p
    pat = args[0] if args else ""
    lines = text.split("\n")
    if text.endswith("\n"):
        lines = lines[:-1]
    if text == "":
        lines = []
    return "".join(l + "\n" for l in lines if pat in l)


def gen(rng, g):
    pat = "".join(rng.choice("ab") for _ in range(rng.randint(0, 2)))
    lines = ["".join(rng.choice("ab x") for _ in range(rng.randint(0, 6))) for _ in range(rng.randint(0, 5))]
    text = "\n".join(lines) + rng.choice(["", "\n"])
    args = [pat] if rng.random() < 0.9 else []
    if rng.random() < 0.2:
        args.append("extra")
    return (args, text)
