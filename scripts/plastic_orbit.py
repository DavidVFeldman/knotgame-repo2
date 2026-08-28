"""The knot game at the plastic number, in exact ZZ[rho] coordinates.

A point is (a, b, c) standing for (a + b*rho + c*rho^2)/2, where rho^3 = rho + 1.
The two branch maps are the ones of `RequestProject/PlasticOrbit.lean`:

    tf0 (a,b,c) = (c, a+c, b)          (x |-> rho x)
    tf1 (a,b,c) = (c+2, a+c-2, b)      (x |-> rho x - (rho-1))

Comparisons are decided with a 60-digit decimal value of rho, which is far more
than the ~1e-3 separation of the orbit points.

Outputs: the orbit of 1/2, the transition tables for the three moves, the number
of reachable configurations, the largest knot count, and the least depth at
which each knot count appears.
"""
from decimal import Decimal, getcontext

getcontext().prec = 60

# rho: the real root of x^3 = x + 1, by Newton's method in Decimal.
RHO = Decimal(1)
for _ in range(200):
    RHO = RHO - (RHO ** 3 - RHO - 1) / (3 * RHO ** 2 - 1)

R = 1 / RHO           # r = 1/rho
G = 1 - R             # g = 1 - r


def val(t):
    a, b, c = t
    return (Decimal(a) + Decimal(b) * RHO + Decimal(c) * RHO * RHO) / 2


def tf0(t):
    a, b, c = t
    return (c, a + c, b)


def tf1(t):
    a, b, c = t
    return (c + 2, a + c - 2, b)


def orbit():
    seen = [(1, 0, 0)]
    stack = [(1, 0, 0)]
    while stack:
        t = stack.pop()
        for u in (tf0(t), tf1(t)):
            v = val(u)
            if 0 < v < 1 and u not in seen:
                seen.append(u)
                stack.append(u)
    return sorted(seen, key=val)


ORB = orbit()
IDX = {t: i for i, t in enumerate(ORB)}


def transitions():
    """For each move, the list of images: None if the point dies."""
    tabs = {}
    for m in "LMR":
        tab = []
        for t in ORB:
            x = val(t)
            if m == "L":
                tab.append(IDX[tf1(t)] if x > G else None)
            elif m == "R":
                tab.append(IDX[tf0(t)] if x < R else None)
            else:
                if x < R / 2:
                    tab.append(IDX[tf0(t)])
                elif x > 1 - R / 2:
                    tab.append(IDX[tf1(t)])
                else:
                    tab.append(None)
        tabs[m] = tab
    return tabs


TAB = transitions()
HALF = IDX[(1, 0, 0)]


def step(m, cfg):
    out = {TAB[m][i] for i in cfg if TAB[m][i] is not None}
    if m == "M":
        out.add(HALF)
    return frozenset(out)


def bfs():
    layer = {frozenset(): ()}
    seen = dict(layer)
    depth = 0
    first = {}
    best = 0
    while layer:
        depth += 1
        nxt = {}
        for cfg, w in layer.items():
            for m in "LMR":
                d = step(m, cfg)
                if d not in seen:
                    seen[d] = w + (m,)
                    nxt[d] = w + (m,)
        layer = nxt
        for cfg, w in layer.items():
            k = len(cfg)
            if k not in first:
                first[k] = (depth, "".join(w))
            best = max(best, k)
    return seen, first, best


if __name__ == "__main__":
    print(f"orbit points: {len(ORB)}")
    seen, first, best = bfs()
    print(f"reachable configurations: {len(seen)}")
    print(f"max knots: {best}")
    for k in sorted(first):
        print(f"  first depth with {k} knots: {first[k][0]}   word={first[k][1]}")
