"""Generate a Lean certificate for the doubling lemma at lam = 3/2.

Certificate: a list of cells (p, q, u, v) with p_0 = a, q_last = b, cells
consecutive (q_i = p_{i+1}), u, v distinct words of length T, and the image of
[p,q] under both words contained in [a,b].  Cells are chosen greedily, so the
list is short.
"""
from fractions import Fraction as F
import sys

lam = F(3, 2)


def qapp(x, w):
    for e in w:
        x = lam * x - e * (lam - 1)
    return x


def words(T):
    out = [()]
    for _ in range(T):
        out = [w + (e,) for w in out for e in (0, 1)]
    return out


def greedy(T, a, b, k=2):
    W = words(T)
    L = lam ** T
    cells = []
    p = a
    guard = 0
    while p < b:
        guard += 1
        if guard > 5000:
            return None
        cand = []
        for w in W:
            if qapp(p, w) >= a:
                # largest q with qapp(q,w) <= b : qapp(q,w) = L*q - c, c = L*p - qapp(p,w)
                c = L * p - qapp(p, w)
                qmax = (b + c) / L
                if qmax > p:
                    cand.append((qmax, w))
        cand.sort(key=lambda t: -t[0])
        # need k words valid on the whole cell; dedupe identical images
        seen, chosen = set(), []
        for qmax, w in cand:
            v = qapp(p, w)
            if v in seen:
                continue
            seen.add(v)
            chosen.append((qmax, w))
            if len(chosen) == k:
                break
        if len(chosen) < k:
            return None
        q = min(qm for qm, _ in chosen)
        cells.append((p, q, [w for _, w in chosen]))
        p = q
    return cells


def fmt_q(x):
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else f"{x.numerator}"


def fmt_w(w):
    return "[" + ",".join(str(e) for e in w) + "]"


if __name__ == "__main__":
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    a = F(sys.argv[3]) if len(sys.argv) > 3 else F(1, 4)
    b = F(sys.argv[4]) if len(sys.argv) > 4 else F(3, 4)
    cells = greedy(T, a, b, k)
    if cells is None:
        print("no certificate")
        sys.exit()
    print(f"-- T = {T}, J = [{a},{b}], {len(cells)} cells, {k} words each")
    for (p, q, ws) in cells:
        print("  (" + fmt_q(p) + ", " + fmt_q(q) + ", " +
              ", ".join(fmt_w(w) for w in ws) + "),")
