import re


def solve(text):
    total = 0
    for n, line in enumerate(text.split("\n"), 1):
        if line == "" or line.startswith("#"):
            continue
        key, eq, value = line.partition("=")
        if not eq:
            return {"err": f"line {n}: missing '='"}
        if key == "":
            return {"err": f"line {n}: empty key"}
        if not re.fullmatch(r"-?[0-9]+", value):
            return {"err": f"line {n}: bad value"}
        total += int(value)
    return {"ok": total}


def gen(rng, g):
    good = ["a=1", "max=10", "x=-3", "k=007", "# c=d", "#", "", "long_key=12345678901234"]
    bad = ["b", "=2", "c=", "d=x", "e=1=2", "f= 3", "g=-", " =1", "h=+4"]
    lines = [rng.choice(good) for _ in range(rng.randint(0, 6))]
    if lines and rng.random() < 0.6:
        lines.insert(rng.randrange(len(lines) + 1), rng.choice(bad))
    if rng.random() < 0.2:
        lines.append(rng.choice(bad))
    return "\n".join(lines) + rng.choice(["", "\n"])
