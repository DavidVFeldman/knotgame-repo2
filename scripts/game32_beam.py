"""Beam search for high-knot-count words of the knot game at lambda = 3/2.

Exhaustive search is out of reach beyond depth ~30 (see `game32_records.py`),
but a *witness* word does not need exhaustiveness: any word the search returns
is checked afterwards in Lean by kernel arithmetic.  This script keeps, at each
depth, the `beam` best configurations, ranked by knot count and then by
diameter (clustered configurations survive better, since one move deletes one
interval).

Usage:  python3 scripts/game32_beam.py [max_depth] [beam]
"""
import sys

L, M, R = 0, 1, 2
NAMES = "LMR"


def step(c, j, S):
    p = 1 << j
    T = []
    for A in S:
        a3 = 3 * A
        if c == L:
            if p < a3:
                T.append(a3 - p)
        elif c == R:
            if a3 < 2 * p:
                T.append(a3)
        else:
            if a3 < p:
                T.append(a3)
            elif 2 * p < a3:
                T.append(a3 - p)
    if c == M:
        T.append(p)
    return frozenset(T)


def key(S, j):
    if not S:
        return (0, 0)
    return (-len(S), (max(S) - min(S)) / float(1 << j))


def search(maxdepth, beam):
    layer = {frozenset(): ()}
    best = 0
    for j in range(maxdepth):
        nxt = {}
        for S, w in layer.items():
            for c in (L, M, R):
                T = step(c, j, S)
                if T not in nxt:
                    nxt[T] = w + (c,)
        items = sorted(nxt.items(), key=lambda kv: key(kv[0], j + 1))
        layer = dict(items[:beam])
        m = max(len(S) for S in layer)
        if m > best:
            best = m
            S0, w0 = min(((S, w) for S, w in layer.items() if len(S) == m),
                         key=lambda kv: kv[1])
            print(f"*** depth {j+1}: k={m} word={''.join(NAMES[c] for c in w0)}")
            print(f"    config numerators over 2^{j+1}: {sorted(S0)}", flush=True)
        print(f"depth {j+1}: beam {len(layer)}, max knots {m}", flush=True)
    return layer


if __name__ == "__main__":
    md = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    bw = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    search(md, bw)
