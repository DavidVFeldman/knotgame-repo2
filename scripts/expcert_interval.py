"""Certificate generator for the doubling lemma uniformly over a lam-interval.

For lam in [l0,l1] and x in [p,q] the image of x under a branch word is enclosed
by interval arithmetic:

  branch 0:  [l0*lo, l1*hi]                (valid when 0 <= lo, 0 <= hi)
  branch 1:  [l1*lo - l1 + 1, l0*hi - l0 + 1]   (valid when lo <= 1, hi <= 1)

Both rules keep the lower endpoint a function of `lo` alone and the upper
endpoint a function of `hi` alone, so each is affine and increasing.
"""
from fractions import Fraction as F
import sys


def step_lo(e, lo, l0, l1):
    return l0 * lo if e == 0 else l1 * lo - l1 + 1


def step_hi(e, hi, l0, l1):
    return l1 * hi if e == 0 else l0 * hi - l0 + 1


def enclose(w, p, q, l0, l1):
    """Interval enclosure of the image of [p,q]; None if the invariant
    0 <= lo, hi <= 1 fails somewhere (so the rules above may be invalid)."""
    lo, hi = p, q
    for e in w:
        if lo < 0 or hi > 1 or lo > hi:
            return None
        lo, hi = step_lo(e, lo, l0, l1), step_hi(e, hi, l0, l1)
    if lo < 0 or hi > 1 or lo > hi:
        return None
    return lo, hi


def hi_affine(w, l0, l1):
    """upper endpoint as A*q + B."""
    A, B = F(1), F(0)
    for e in w:
        if e == 0:
            A, B = l1 * A, l1 * B
        else:
            A, B = l0 * A, l0 * B - l0 + 1
    return A, B


def words(T):
    out = [()]
    for _ in range(T):
        out = [w + (e,) for w in out for e in (0, 1)]
    return out


def greedy(T, a, b, l0, l1, k=2):
    W = words(T)
    cells = []
    p = a
    guard = 0
    while p < b:
        guard += 1
        if guard > 3000:
            return None
        cand = []
        for w in W:
            enc = enclose(w, p, p, l0, l1)
            if enc is None or enc[0] < a:
                continue
            A, B = hi_affine(w, l0, l1)
            qmax = (b - B) / A
            if qmax > p and enclose(w, p, qmax, l0, l1) is not None:
                cand.append((qmax, w))
        cand.sort(key=lambda t: -t[0])
        chosen, seen = [], set()
        for qm, w in cand:
            if w in seen:
                continue
            seen.add(w)
            chosen.append((qm, w))
            if len(chosen) == k:
                break
        if len(chosen) < k:
            return None
        q = min(qm for qm, _ in chosen)
        # round the endpoint down to a coarse grid, to keep the certificate small
        D = 10 ** 6
        qr = F(int(q * D), D)
        if qr > p:
            q = qr
        cells.append((p, q, [w for _, w in chosen]))
        p = q
    return cells


def fmt_q(x):
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else f"{x.numerator}"


if __name__ == "__main__":
    a, b = F(1, 4), F(3, 4)
    if len(sys.argv) > 1 and sys.argv[1] == "gen":
        T = int(sys.argv[2]); l0 = F(sys.argv[3]); l1 = F(sys.argv[4])
        cells = greedy(T, a, b, l0, l1)
        if cells is None:
            print("no certificate")
        else:
            print(f"-- T = {T}, lam in [{l0},{l1}], J = [{a},{b}], {len(cells)} cells")
            for (p, q, ws) in cells:
                print("  (" + fmt_q(p) + ", " + fmt_q(q) + ", " +
                      ", ".join("[" + ",".join(map(str, w)) + "]" for w in ws) + "),")
    else:
        for T in (5, 6, 7):
            for hw in (F(1, 1000), F(1, 200), F(1, 100), F(1, 50), F(1, 25), F(1, 10)):
                l0, l1 = F(3, 2) - hw, F(3, 2) + hw
                cells = greedy(T, a, b, l0, l1)
                print(T, f"±{hw}", "cells:", None if cells is None else len(cells))
                sys.stdout.flush()
