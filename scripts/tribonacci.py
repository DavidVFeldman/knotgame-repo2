"""Exact tribonacci computation: orbit of 1/2, transition tables,
configuration closure, exact maximum, and depth of first attainment d(k).

lam^3 = lam^2 + lam + 1, lam ~ 1.8392867552141612.
Points are x = (A + B*lam + C*lam^2)/2 with A,B,C integers.
Signs are decided with a rational bracket for lam of high precision.
"""
from fractions import Fraction

lo, hi = Fraction(18, 10), Fraction(19, 10)
f = lambda t: t**3 - t**2 - t - 1
for _ in range(300):
    mid = (lo + hi) / 2
    if f(mid) < 0:
        lo = mid
    else:
        hi = mid
LAM_LO, LAM_HI = lo, hi
print("lam in", float(LAM_LO), float(LAM_HI))


def val(t):
    A, B, C = t
    v_lo = A + B * (LAM_LO if B > 0 else LAM_HI) + C * ((LAM_LO**2) if C > 0 else (LAM_HI**2))
    v_hi = A + B * (LAM_HI if B > 0 else LAM_LO) + C * ((LAM_HI**2) if C > 0 else (LAM_LO**2))
    return v_lo, v_hi


def sgn(t):
    A, B, C = t
    if A == 0 and B == 0 and C == 0:
        return 0
    lo, hi = val(t)
    assert lo > 0 or hi < 0, ("undecided sign", t)
    return 1 if lo > 0 else -1


mulL = lambda A, B, C: (C, A + C, B + C)
f0 = lambda p: mulL(*p)
f1 = lambda p: (lambda t: (t[0] + 2, t[1] - 2, t[2]))(mulL(*p))

ltr = lambda A, B, C: (A + 2, B + 2, C - 2)
gtg = lambda A, B, C: (A - 4, B - 2, C + 2)
lth = lambda A, B, C: (A + 1, B + 1, C - 1)
gth = lambda A, B, C: (A - 3, B - 1, C + 1)


def moves(p):
    out = {}
    if sgn(gtg(*p)) > 0:
        out['L'] = f1(p)
    if sgn(ltr(*p)) < 0:
        out['R'] = f0(p)
    if sgn(lth(*p)) < 0:
        out['M'] = f0(p)
    elif sgn(gth(*p)) > 0:
        out['M'] = f1(p)
    return out


half = (1, 0, 0)
O = {half}
front = {half}
while front:
    nf = set()
    for p in front:
        for q in moves(p).values():
            if q not in O:
                O.add(q)
                nf.add(q)
    front = nf
    assert len(O) < 10000

pts = sorted(O, key=lambda t: float(val(t)[0]))
print("orbit size", len(O))
for i, p in enumerate(pts):
    lo_, hi_ = val(p)
    print(i, p, float(lo_) / 2, moves(p))

idx = {p: i for i, p in enumerate(pts)}
TL, TR, TM = [], [], []
for p in pts:
    mv = moves(p)
    TL.append(idx[mv['L']] if 'L' in mv else -1)
    TR.append(idx[mv['R']] if 'R' in mv else -1)
    TM.append(idx[mv['M']] if 'M' in mv else -1)
print("TL", TL)
print("TR", TR)
print("TM", TM)
print("half index", idx[half])

born = 1 << idx[half]


def stepmask(mask, tab, add):
    m = 0
    i = 0
    mm = mask
    while mm:
        if mm & 1 and tab[i] >= 0:
            m |= 1 << tab[i]
        mm >>= 1
        i += 1
    return m | add


layer = {0}
seen = {0}
depth = 0
maxcard = {}
while depth <= 20:
    maxcard[depth] = max(bin(s).count('1') for s in layer)
    nxt = set()
    for s in layer:
        for t in (stepmask(s, TL, 0), stepmask(s, TR, 0), stepmask(s, TM, born)):
            nxt.add(t)
    seen |= nxt
    layer = nxt
    depth += 1
print("reachable configurations", len(seen))
print("max card", max(bin(s).count('1') for s in seen))
print("max card by depth", maxcard)


def bits(s):
    return sorted(i for i in range(len(pts)) if s >> i & 1)


print("configs:", sorted([bits(s) for s in seen], key=lambda b: (len(b), b)))

from itertools import product
for k in (1, 2, 3, 4):
    found = None
    for n in range(0, 10):
        for w in product('LRM', repeat=n):
            s = 0
            for ch in w:
                s = stepmask(s, {'L': TL, 'R': TR, 'M': TM}[ch], born if ch == 'M' else 0)
            if bin(s).count('1') >= k:
                found = (n, ''.join(w), bits(s))
                break
        if found:
            break
    print("k =", k, "d(k) =", found)
