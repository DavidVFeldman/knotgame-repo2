"""Exhaustive breadth-first search of the knot game at lambda = 3/2.

Exact integer model (the replica of `RequestProject/RunRational.lean`): a
configuration after j moves is a frozenset of numerators over 2^j.  States are
deduplicated at each depth.  Prints, for each depth, the number of reachable
configurations and the largest knot count seen so far, together with a witness
word for each new record.

Usage:  python3 scripts/game32_bfs.py [max_depth]
"""
import sys

L, M, R = 0, 1, 2
NAMES = "LMR"


def survives(c, j, A):
    if c == L:
        return 2 ** j < 3 * A
    if c == M:
        return 3 * A < 2 ** j or 2 * 2 ** j < 3 * A
    return 3 * A < 2 * 2 ** j


def act(c, j, A):
    if c == L:
        return 3 * A - 2 ** j
    if c == M:
        return 3 * A if 3 * A < 2 ** j else 3 * A - 2 ** j
    return 3 * A


def step(c, j, S):
    T = {act(c, j, A) for A in S if survives(c, j, A)}
    if c == M:
        T.add(2 ** j)
    return frozenset(T)


def bfs(maxdepth):
    layer = {frozenset(): ()}
    best = 0
    for j in range(maxdepth):
        nxt = {}
        for S, w in layer.items():
            for c in (L, M, R):
                T = step(c, j, S)
                if T not in nxt:
                    nxt[T] = w + (c,)
        layer = nxt
        m = max(len(S) for S in layer)
        if m > best:
            best = m
            wit = min((w for S, w in layer.items() if len(S) == m))
            print(f"depth {j+1}: NEW RECORD k={m}  word={''.join(NAMES[c] for c in wit)}")
        print(f"depth {j+1}: {len(layer)} configurations, max knots {m}", flush=True)
    return layer


if __name__ == "__main__":
    bfs(int(sys.argv[1]) if len(sys.argv) > 1 else 20)
