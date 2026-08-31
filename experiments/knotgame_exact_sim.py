"""Exact knot-game simulator over Z[lambda] for algebraic lambda.

Positions live in Q(lambda) as coefficient vectors over the basis
1, lam, ..., lam^(d-1).  Every survival test is turned into a SIGN test on an
element of Z[lambda], so no comparison is ever decided by rounding -- which is
what corrupted the floating-point version (it reported 4 knots at the golden
ratio, where the true maximum is 2, because the orbit lands exactly on the
boundary r/2 and `<` then decides a tie arbitrarily).
"""
from fractions import Fraction as F
import mpmath as mp, sys
sys.setrecursionlimit(20000)
mp.mp.dps = 60

class Field:
    def __init__(self, red, lam):
        self.d = len(red); self.red = red      # lam^d = sum red[i] lam^i
        self.lam = lam
        self.pw = [lam**i for i in range(self.d)]
    def mul_lam(self, c):
        top = c[-1]
        out = [F(0)] + list(c[:-1])
        if top:
            for i in range(self.d): out[i] += top*self.red[i]
        return tuple(out)
    def val(self, c):
        return sum(mp.mpf(x.numerator)/x.denominator*p for x, p in zip(c, self.pw))
    def sign(self, c):
        if all(x == 0 for x in c): return 0
        v = self.val(c)
        if abs(v) < mp.mpf('1e-40'): raise RuntimeError('precision')
        return 1 if v > 0 else -1

def const(K, q): return tuple([F(q)] + [F(0)]*(K.d-1))
def add(a, b): return tuple(x+y for x, y in zip(a, b))
def sub(a, b): return tuple(x-y for x, y in zip(a, b))
def smul(s, a): return tuple(F(s)*x for x in a)

def best_count(K, N, seed=0):
    ONE = const(K, 1); HALF = const(K, F(1,2))
    LAM = K.mul_lam(ONE); LAMM1 = sub(LAM, ONE)
    TWOLAM = smul(2, LAM); TWOLAMM1 = sub(TWOLAM, ONE)
    lt = lambda a, b: K.sign(sub(a, b)) < 0
    gt = lambda a, b: K.sign(sub(a, b)) > 0
    best = seed
    def rec(state, d):
        nonlocal best
        if len(state) > best: best = len(state)
        if d == N or len(state) + (N-d) <= best: return
        # R : x < 1/lam  <=>  lam*x < 1 ;  x -> lam*x
        rec(tuple(K.mul_lam(x) for x in state if lt(K.mul_lam(x), ONE)), d+1)
        # L : x > 1-1/lam <=> lam*x > lam-1 ; x -> lam*x-(lam-1)
        rec(tuple(sub(K.mul_lam(x), LAMM1) for x in state
                  if gt(K.mul_lam(x), LAMM1)), d+1)
        # M : 2*lam*x < 1  or  2*lam*x > 2*lam-1 ; births a knot at 1/2
        surv = []
        for x in state:
            t = smul(2, K.mul_lam(x))
            if lt(t, ONE):        surv.append(K.mul_lam(x))
            elif gt(t, TWOLAMM1): surv.append(sub(K.mul_lam(x), LAMM1))
        rec(tuple(surv) + (HALF,), d+1)
    rec((), 0)
    return best

FIELDS = {   # lam^d = sum red[i] lam^i
 'golden':      ([F(1), F(1)],            mp.findroot(lambda x: x**2-x-1, 1.6)),
 'plastic':     ([F(1), F(1), F(0)],      mp.findroot(lambda x: x**3-x-1, 1.32)),
 'supergolden': ([F(1), F(0), F(1)],      mp.findroot(lambda x: x**3-x**2-1, 1.46)),
 'tribonacci':  ([F(1), F(1), F(1)],      mp.findroot(lambda x: x**3-x**2-x-1, 1.84)),
}

if __name__ == '__main__':
    # Progressive seeding: counts are monotone in depth, so the previous
    # depth's answer is a sound initial value for the alpha-beta style prune.
    want = {'golden': 2, 'tribonacci': 3, 'supergolden': 4, 'plastic': 7}
    for name, depths in [('golden', (8, 11, 14)), ('tribonacci', (8, 11, 14)),
                         ('supergolden', (10, 13, 16)), ('plastic', (9, 12, 15))]:
        red, lam = FIELDS[name]; K = Field(red, lam); b = 0
        for N in depths:
            b = best_count(K, N, b)
        print('%-12s lam=%.6f  depth %d -> %d   paper N = %d'
              % (name, float(lam), depths[-1], b, want[name]), flush=True)
