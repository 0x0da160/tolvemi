import re


def solve(text):
    words = [w for w in re.split("[ \n]", text) if w]
    digits = sum(1 for w in words if any("0" <= c <= "9" for c in w))
    return (digits, all(len(w) <= 8 for w in words))


def gen(rng, g):
    pool = ["a", "word", "x9", "2024", "abcdefgh", "abcdefghi", "v1.2", "high-score", "été", "R2D2", "-", "tab\there"]
    seps = [" ", "  ", "\n", " \n "]
    out = rng.choice(["", " ", "\n"])
    for _ in range(rng.randint(0, 6)):
        out += rng.choice(pool) + rng.choice(seps)
    return out[: len(out) - rng.randint(0, 1)]
