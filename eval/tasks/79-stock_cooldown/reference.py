def solve(ps):
    hold = None  # best profit while holding a share
    sold = None  # best profit having sold today
    rest = 0     # best profit, not holding, free to buy tomorrow
    for p in ps:
        new_hold = rest - p if hold is None else max(hold, rest - p)
        new_sold = None if hold is None else hold + p
        new_rest = rest if sold is None else max(rest, sold)
        hold, sold, rest = new_hold, new_sold, new_rest
    return rest if sold is None else max(rest, sold)

def gen(rng, g):
    return [rng.randint(0, 10) for _ in range(rng.randint(0, 10))]
