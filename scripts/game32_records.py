"""Search for record words of the knot game at lambda = 3/2.

Same exact integer model as `game32_bfs.py`, but with *dominance pruning*: the
one-step map on configurations is monotone for inclusion (a knot survives and
moves independently of the others, and the newborn knot is added regardless),
so a configuration contained in another one at the same depth can never do
better than it in the future and may be discarded.  Keeping only the maximal
configurations of each layer is therefore sound for the question "what is the
largest knot count reachable at depth n, and by which word".

Usage:  python3 scripts/game32_records.py [max_depth]
"""
import sys

L, M, R = 0, 1, 2
NAMES = "LMR"


def step(c, j, S):
    p = 1 << j
    T = set()
    for A in S:
        a3 = 3 * A
        if c == L:
            if p < a3:
                T.add(a3 - p)
        elif c == R:
            if a3 < 2 * p:
                T.add(a3)
        else:
            if a3 < p:
                T.add(a3)
            elif 2 * p < a3:
                T.add(a3 - p)
    if c == M:
        T.add(p)
    return frozenset(T)


def maximal(layer):
    """Keep only the configurations not contained in a different one."""
    items = sorted(layer.items(), key=lambda kv: -len(kv[0]))
    kept = []
    for S, w in items:
        if not any(S <= T for T, _ in kept):
            kept.append((S, w))
    return dict(kept)


def search(maxdepth):
    layer = {frozenset(): ()}
    best = 0
    for j in range(maxdepth):
        nxt = {}
        for S, w in layer.items():
            for c in (L, M, R):
                T = step(c, j, S)
                if T not in nxt:
                    nxt[T] = w + (c,)
        layer = maximal(nxt)
        m = max(len(S) for S in layer)
        if m > best:
            best = m
            wit = min(w for S, w in layer.items() if len(S) == m)
            print(f"*** depth {j+1}: k={m} word={''.join(NAMES[c] for c in wit)}")
        print(f"depth {j+1}: {len(layer)} maximal configurations, max knots {m}",
              flush=True)
    return layer


if __name__ == "__main__":
    search(int(sys.argv[1]) if len(sys.argv) > 1 else 52)
