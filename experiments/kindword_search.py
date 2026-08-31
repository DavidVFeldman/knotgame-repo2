"""
Search for a periodic kind word with a terminal M (paper prop:kindyield).

Such a word at any lambda would give N_lambda = infinity outright, and it is
the sharpest open form of the unboundedness question: it asks for one finite
word.

The orbit of 1/2 under the periodic word is propagated as an INTERVAL in x
over an INTERVAL of lambda, in exact fixed-point arithmetic with P fractional
bits and directed rounding, so a reported survival depth is a sound statement
about every lambda in the interval.  This is the untrusted half of the usual
pattern: a witness found here would still have to be re-verified by the
kernel.

Two traps, both hit during development, both worth keeping in the code:

1.  BRANCH-1 BOUNDS.  The map is lam*(x-1) + 1, which is INCREASING in x and
    DECREASING in lam.  Its minimum over the box is therefore at
    (lam = B, x = XL) and its maximum at (lam = A, x = XH).  Taking the
    minimum at XH -- the natural-looking mistake -- makes the interval too
    narrow and the search unsound: with that bug eleven words appeared to
    survive to the depth cap, and every one of them was an artifact.

2.  THE KNIFE EDGE.  Maximising survival depth over lambda converges on the
    parameters where the orbit returns exactly to 1/2, i.e. on the roots of
    Littlewood polynomials (paper sec:kind).  Those are precisely the
    parameters cor:noperiodic excludes: the terminal M then lands on 1/2,
    which sits on the boundary of the M-survival condition, and the condition
    is a strict inequality.  In floating point such an orbit can appear to
    survive tens of thousands of steps.  The margin EPS below is what rules
    this out -- survival is required with room to spare, which is also what a
    compactness argument would need in order to pass from "survives to every
    depth" to "survives forever".
"""

import itertools

P = 900
ONE = 1 << P


def fixed(num, den=1):
    return (num << P) // den


def survival_depth(A, B, word, D, EPS):
    """Sound lower bound on the survival depth of 1/2, uniform over [A, B].

    Returns (depth, min_margin).  depth == D means every lambda in [A, B]
    survives D steps with margin at least EPS at every step.
    """
    XL = XH = ONE // 2
    margin = ONE
    for n in range(D):
        move = word[n % len(word)]
        # branch 0: lam*x, increasing in both arguments
        b0_lo = (A * XL) >> P
        b0_hi = -((-(B * XH)) >> P)
        # branch 1: lam*(x-1) + 1, increasing in x, decreasing in lam
        b1_lo = ((B * (XL - ONE)) >> P) + ONE
        b1_hi = (-((-(A * (XH - ONE))) >> P)) + ONE
        if move == 'R':                       # legal iff x < 1/lam
            if not b0_hi < ONE - EPS:
                return n, margin
            margin = min(margin, ONE - b0_hi)
            XL, XH = b0_lo, b0_hi
        elif move == 'L':                     # legal iff x > 1 - 1/lam
            if not b1_lo > EPS:
                return n, margin
            margin = min(margin, b1_lo)
            XL, XH = b1_lo, b1_hi
        else:                                 # M: the middle band is deleted
            if b0_hi < ONE // 2 - EPS:
                margin = min(margin, ONE // 2 - b0_hi)
                XL, XH = b0_lo, b0_hi
            elif b1_lo > ONE // 2 + EPS:
                margin = min(margin, b1_lo - ONE // 2)
                XL, XH = b1_lo, b1_hi
            else:
                return n, margin
        if not (XL > EPS and XH < ONE - EPS):
            return n, margin
    return D, margin


def beam_search(word, lo, hi, D, EPS, width=6, rounds=520):
    """Bisect the lambda interval, keeping the `width` deepest survivors."""
    current = [(lo, hi)]
    best = (0, (lo, hi), 0)
    for _ in range(rounds):
        nxt = []
        for a, b in current:
            mid = (a + b) // 2
            for iv in ((a, mid), (mid, b)):
                d, m = survival_depth(iv[0], iv[1], word, D, EPS)
                if d > best[0]:
                    best = (d, iv, m)
                if d >= D:
                    return d, iv, m
                nxt.append((d, iv))
        if not nxt:
            return best
        nxt.sort(key=lambda t: -t[0])
        current = [iv for _, iv in nxt[:width]]
    return best


def sweep(max_period=6, lo=fixed(102, 100), hi=fixed(133, 100), D=1500,
          eps_den=10 ** 6):
    """All words of period <= max_period ending in M, over [lo, hi]."""
    EPS = ONE // eps_den
    results = []
    for p in range(2, max_period + 1):
        for prefix in itertools.product('LMR', repeat=p - 1):
            word = list(prefix) + ['M']
            d, iv, m = beam_search(word, lo, hi, D, EPS)
            results.append((d, p, ''.join(word), iv, m))
        print('period %d complete' % p, flush=True)
    results.sort(reverse=True)
    return results


if __name__ == '__main__':
    for d, p, w, iv, m in sweep()[:10]:
        print('%-8s period %d  depth %5d  lambda ~ %.12f  margin %.3e'
              % (w, p, d, iv[0] / ONE, m / ONE))
