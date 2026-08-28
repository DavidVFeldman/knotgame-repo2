"""Search for a *variable-return-time* doubling certificate (round 10, T32).

Same interval arithmetic as `scripts/expcert_interval.py` (and the Lean checker
`ExpCert.iok`), but a cell now carries two words of *possibly different* lengths,
both at most `Tmax`, which must **diverge** — disagree at some index below both
lengths.  That is the hypothesis `ExpVar.VDoubling`, and it is what makes a
certificate possible above the golden ratio, where two returns at a *common*
length are too much to ask.

Nothing here is trusted: the Lean kernel re-checks every cell.
"""
from fractions import Fraction as F

BIG = F(10 ** 9)


def cands_upto(Tmax, p, a, b, l0, l1):
    """Every legal word of length `1..Tmax` from the point `p` whose image lies
    in `[a,b]`, paired with the largest right endpoint `q` for which the whole
    enclosure over `[p,q]` stays valid and ends inside `[a,b]`."""
    out = []

    def rec(d, lo, A, B, w, qb):
        if lo < 0:
            return
        q1 = (1 - B) / A
        qb2 = q1 if q1 < qb else qb
        if qb2 < p:
            return
        if d > 0 and lo >= a:
            q = (b - B) / A
            if q > qb2:
                q = qb2
            if q > p:
                out.append((q, tuple(w)))
        if d == Tmax:
            return
        rec(d + 1, l0 * lo, l1 * A, l1 * B, w + [0], qb2)
        rec(d + 1, l1 * lo - l1 + 1, l0 * A, l0 * B - l0 + 1, w + [1], qb2)

    rec(0, p, F(1), F(0), [], BIG)
    return out


def divergent(u, v):
    for i in range(min(len(u), len(v))):
        if u[i] != v[i]:
            return True
    return False


def best_pair(c):
    """The diverging pair maximising the right endpoint of the cell."""
    c = sorted(c, key=lambda t: -t[0])
    for j in range(1, len(c)):
        for i in range(j):
            if divergent(c[i][1], c[j][1]):
                return c[j][0], c[i][1], c[j][1]
    return None


def greedy_var(Tmax, a, b, l0, l1, grid=10 ** 6, maxcells=20000, maxback=200):
    """A chained list of cells tiling `[a,b]`, each with a diverging pair of
    words of length at most `Tmax`; `None` if the greedy fails.

    Where the greedy stalls — at a point from which no diverging pair of length
    at most `Tmax` returns to `[a,b]` — it backtracks, halving the previous
    cell (shrinking a cell keeps it valid, the enclosure being monotone in the
    right endpoint) so that the next cell starts somewhere else.
    """
    cells = []
    p = a
    back = 0
    while p < b:
        if len(cells) > maxcells:
            return None
        bp = best_pair(cands_upto(Tmax, p, a, b, l0, l1))
        q = None
        if bp is not None:
            q, u, v = bp
            if q > b:
                q = b
            qr = F(int(q * grid), grid)
            if qr > p:
                q = qr
            if q <= p:
                q = None
        if q is None:
            # stalled: back off, shrinking the previous cell
            back += 1
            if back > maxback or not cells:
                return None
            pp, qq, uu, vv = cells.pop()
            nq = (pp + qq) / 2
            if nq <= pp:
                return None
            cells.append((pp, nq, uu, vv))
            p = nq
            continue
        cells.append((p, q, list(u), list(v)))
        p = q
    return cells


def cover(L0, L1, Tmax, a, b, maxdepth=14, grid=10 ** 6, maxcells=4000):
    """Adaptively split the parameter interval `[L0,L1]` until every piece
    carries a certificate.  Returns a list `(l0, l1, cells)` or `None`."""
    todo = [(L0, L1, 0)]
    out = []
    while todo:
        l0, l1, d = todo.pop(0)
        cells = greedy_var(Tmax, a, b, l0, l1, grid=grid, maxcells=maxcells)
        if cells is not None:
            out.append((l0, l1, cells))
            continue
        if d >= maxdepth:
            return None
        mid = (l0 + l1) / 2
        D = 10 ** 7
        midr = F(int(mid * D), D)
        if l0 < midr < l1:
            mid = midr
        todo.append((l0, mid, d + 1))
        todo.append((mid, l1, d + 1))
    out.sort(key=lambda t: t[0])
    return out


def fq(x):
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else f"{x.numerator}"


def fw(w):
    return "[" + ",".join(map(str, w)) + "]"


# Note (round 10): a candidate word is kept only when its admissible right
# endpoint is *strictly* to the right of the cell's left endpoint.  Without the
# strictness the greedy stalls at the preimages of the endpoint `1`, where a
# word's enclosure is tight and the cell would be degenerate.
