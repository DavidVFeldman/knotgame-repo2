"""Faster certificate search (round 10).

Same interval arithmetic as `scripts/expcert_interval.py`:

  branch 0:  [l0*lo, l1*hi]
  branch 1:  [l1*lo - l1 + 1, l0*hi - l0 + 1]

with the invariant `0 <= lo <= hi <= 1` maintained at every step, but organised
as a depth-first search over the *tree* of words rather than an enumeration of
all `2^T` of them: a prefix whose lower endpoint has already left `[0,1]` (or
whose cell has already collapsed) is pruned, so the search visits only the
surviving prefixes, of which there are `O((2/lam)^T)` rather than `2^T`.

Two further differences from `expcert_interval.greedy`:

* the largest admissible right endpoint `qmax` of a cell for a given word takes
  the *intermediate* constraints `hi_i <= 1` into account, not only the final
  one — `expcert_interval` computed `qmax` from the final constraint alone and
  then discarded the word if an intermediate one failed;
* the cell endpoints are rounded down to a grid whose fineness is a parameter.

Nothing here is trusted: the Lean kernel re-checks every cell that is written
out.
"""
from fractions import Fraction as F

BIG = F(10 ** 9)


def cands(T, p, a, b, l0, l1):
    """All words of length `T` legal from the point `p` whose image at `p` lies
    in `[a,b]`, each paired with the largest `q` for which the enclosure over
    `[p,q]` stays valid and ends inside `[a,b]`.

    The lower endpoint of the enclosure depends only on `p`; the upper endpoint
    is the affine function `A*q + B` of the right end `q` of the cell.
    """
    out = []

    def rec(d, lo, A, B, w, qb):
        if d == T:
            if lo < a:
                return
            q = (b - B) / A
            if q > qb:
                q = qb
            if q > p:
                out.append((q, tuple(w)))
            return
        if lo < 0:
            return
        q1 = (1 - B) / A
        qb2 = q1 if q1 < qb else qb
        if qb2 < p:
            return
        rec(d + 1, l0 * lo, l1 * A, l1 * B, w + [0], qb2)
        rec(d + 1, l1 * lo - l1 + 1, l0 * A, l0 * B - l0 + 1, w + [1], qb2)

    rec(0, p, F(1), F(0), [], BIG)
    return out


def greedy(T, a, b, k, l0, l1, grid=10 ** 6, maxcells=20000):
    """A chained list of cells tiling `[a,b]`, each with `k` distinct words of
    length `T`; `None` if the greedy fails."""
    cells = []
    p = a
    while p < b:
        if len(cells) > maxcells:
            return None
        c = cands(T, p, a, b, l0, l1)
        if len(c) < k:
            return None
        c.sort(key=lambda t: -t[0])
        chosen = c[:k]
        q = min(x for x, _ in chosen)
        if q > b:
            q = b
        qr = F(int(q * grid), grid)
        if qr > p:
            q = qr
        if q <= p:
            return None
        cells.append((p, q, [list(w) for _, w in chosen]))
        p = q
    return cells


def fq(x):
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else f"{x.numerator}"


def fw(w):
    return "[" + ",".join(map(str, w)) + "]"
