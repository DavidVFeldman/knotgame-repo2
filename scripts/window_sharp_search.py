"""Search for a {-1,0,1} power series with constant term 1 witnessing failure of
delta-transversality just beyond the certified window [1/2, 667/1000].

We look for a finite coefficient vector c in {-1,0,1}^N with c_0 = 1 and a
rational x in (667/1000, 67/100] such that

    |g(x)| <= 1/1000    and    g'(x) >= -1/1000,

where g(x) = sum_i c_i x^i (the tail is identically zero, so g is a polynomial).

The program is untrusted: whatever it finds is re-checked by the Lean kernel
over exact rationals.
"""

from fractions import Fraction
import sys

EPS = Fraction(1, 1000)


def search(x: Fraction, N: int):
    xs = [x ** i for i in range(N + 1)]
    # tail bounds: TS[k] = sum_{i=k+1}^N x^i, TD[k] = sum_{i=k+1}^N i x^(i-1)
    TS = [Fraction(0)] * (N + 2)
    TD = [Fraction(0)] * (N + 2)
    for k in range(N - 1, -1, -1):
        TS[k] = TS[k + 1] + xs[k + 1]
        TD[k] = TD[k + 1] + (k + 1) * xs[k]

    sol = None

    def dfs(k, S, D, coeffs):
        nonlocal sol
        if sol is not None:
            return
        if k > N:
            if abs(S) <= EPS and D >= -EPS:
                sol = list(coeffs)
            return
        # prune
        if abs(S) - TS[k - 1] > EPS:
            return
        if D + TD[k - 1] < -EPS:
            return
        for c in (1, 0, -1):
            coeffs.append(c)
            dfs(k + 1, S + c * xs[k], D + c * k * xs[k - 1], coeffs)
            coeffs.pop()
            if sol is not None:
                return

    dfs(1, Fraction(1), Fraction(0), [1])
    return sol


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    lo, hi = Fraction(667, 1000), Fraction(67, 100)
    den = 10000
    cands = []
    n = lo.numerator * den // lo.denominator + 1
    while Fraction(n, den) <= hi:
        cands.append(Fraction(n, den))
        n += 1
    for x in cands:
        sol = search(x, N)
        print(x, sol, flush=True)
        if sol is not None:
            xs = [x ** i for i in range(N + 1)]
            g = sum(c * xs[i] for i, c in enumerate(sol))
            gp = sum(i * c * xs[i - 1] for i, c in enumerate(sol) if i > 0)
            print("  g =", float(g), " g' =", float(gp))
            print("  coeffs =", sol)
            return


if __name__ == "__main__":
    main()
