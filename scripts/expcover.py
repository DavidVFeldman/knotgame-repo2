"""Search for a double-covering certificate giving an exponential lower bound
on the number of surviving branch words at lam = 3/2.

Branch maps f0(x)=lam x, f1(x)=lam x-(lam-1) on (0,1); a word of length T sends
x to lam^T x - c(w).  We want an interval J=[a,b] containing 1/2 and T with:
every x in J admits at least two words of length T whose image lies in J.

All arithmetic is done in units of 2^-T (so constants are integers).
"""
from fractions import Fraction as F
from bisect import bisect_left, bisect_right
import sys

lam = F(3, 2)


def cvals(T):
    """dict: integer 2^T*c(w) -> witness word (tuple of digits, applied left to right)."""
    cur = {0: ()}          # keys are 2^k * c after k steps
    for k in range(T):
        nxt = {}
        for c, w in cur.items():
            # c is 2^k * c_k ; c_{k+1} = (3/2) c_k + e/2 ; 2^{k+1} c_{k+1} = 3c + e*2^k
            for e in (0, 1):
                c2 = 3 * c + e * (2 ** k)
                if c2 not in nxt:
                    nxt[c2] = w + (e,)
        cur = nxt
    return cur


def min_count(T, a, b, keys):
    """min over x in [a,b] of #{c in C : a <= lam^T x - c <= b}, integer units."""
    S = 2 ** T
    A, B = a * S, b * S          # Fractions, integers if a,b have denominator | S
    L = F(3, 2) ** T
    ylo, yhi = L * a * S, L * b * S
    events = [ylo, yhi]
    for c in keys:
        for t in (c + A, c + B):
            if ylo <= t <= yhi:
                events.append(t)
    events = sorted(set(events))
    best = None
    arg = None
    pts = []
    for i, y in enumerate(events):
        pts.append(y)
        if i + 1 < len(events):
            pts.append((y + events[i + 1]) / 2)
    for y in pts:
        lo = y - B
        hi = y - A
        i = bisect_left(keys, lo)
        j = bisect_right(keys, hi)
        k = j - i
        if best is None or k < best:
            best, arg = k, y
    return best, arg


def main():
    for T in range(5, 15):
        C = cvals(T)
        keys = sorted(C)
        out = []
        for (a, b) in [(F(1,3),F(2,3)), (F(2,5),F(3,5)), (F(1,4),F(3,4)), (F(3,10),F(7,10)),
                       (F(1,5),F(4,5)), (F(9,20),F(11,20)), (F(1,8),F(7,8))]:
            m, arg = min_count(T, a, b, keys)
            out.append(f"[{a},{b}]:{m}")
        print(T, len(keys), "  ".join(out)); sys.stdout.flush()


main()
