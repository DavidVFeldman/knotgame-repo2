"""Exact integer replica of the Lean checker for T9.

All arithmetic is on natural/integer numbers of at most ~70 bits.

  x-values             : denominator Q
  bound quantities     : denominator S
  node values (g, p)   : denominator S, with a uniform slack for the rounding
                         committed by the (floor-rounded) powers XG, XP.

The only roundings are floor (for XG, XP: safe, absorbed by the slack) and
ceiling (for the bounds: safe, upward).
"""
import json
import sys

D = int(sys.argv[1]) if len(sys.argv) > 1 else 48
Q = 1024000000                # = 2^16 * 5^6
S = 10**18
DELTA = 10**15                # delta = 1/1000 at scale S
SLA = 3 * (D + 1)
SLB = 3 * D * (D + 1)
A0 = Q // 2                   # 1/2
B0 = 667 * (Q // 1000)        # 667/1000


def cdiv(x, d):
    return (x + d - 1) // d


def thresholds(an, bn):
    BP = [S]
    for i in range(D + 1):
        BP.append(cdiv(BP[i] * bn, Q))
    DS = [0]
    for i in range(D + 1):
        DS.append(DS[i] + (i + 1) * BP[i])
    DD = [0]
    for i in range(D + 1):
        DD.append(DD[i] + (i + 1) * i * BP[max(i - 1, 0)])
    w = bn - an
    TA, TB = [], []
    for i in range(D + 1):
        T1 = cdiv(BP[i + 1] * Q, Q - bn)
        T2 = cdiv((i + 1) * BP[i] * Q * Q, (Q - bn) ** 2)
        VG = cdiv(DS[i] * w, 2 * Q)
        VP = cdiv(DD[i] * w, 2 * Q)
        TA.append(DELTA + VG + T1 + SLA)
        TB.append(DELTA + VP + T2 + SLB)
    return TA, TB


def run_cell(an, bn, cap=200_000):
    mn = (an + bn) // 2
    assert (an + bn) % 2 == 0
    TA, TB = thresholds(an, bn)
    XG = [S]
    for i in range(D):
        XG.append(XG[i] * mn // Q)
    XP = [0] + [i * XG[i - 1] for i in range(1, D + 1)]
    nodes = 0
    layer = [(S, 0)] if (S <= TA[0] and TB[0] >= 0) else []
    for i in range(1, D + 1):
        nxt = []
        xg, xp, ta, tb = XG[i], XP[i], TA[i], TB[i]
        for (g, p) in layer:
            for c in (-1, 0, 1):
                g2 = g + c * xg
                p2 = p + c * xp
                nodes += 1
                if abs(g2) <= ta and p2 + tb >= 0:
                    nxt.append((g2, p2))
        layer = nxt
        if nodes > cap:
            return None, nodes
        if not layer:
            return True, nodes
    return (len(layer) == 0), nodes


def adaptive(a, b, granule):
    todo = [(a, b)]
    cells = []
    total = 0
    while todo:
        x, y = todo.pop()
        ok, n = run_cell(x, y)
        if ok:
            cells.append((x, y, n))
            total += n
            continue
        mid = (x + y) // 2
        mid -= mid % granule
        if mid <= x or mid >= y:
            raise RuntimeError(f"cannot subdivide {x} {y}")
        todo.append((mid, y))
        todo.append((x, mid))
    cells.sort()
    return cells, total


if __name__ == '__main__':
    granule = 2 ** 6 * 5 ** 3
    assert A0 % granule == 0 and B0 % granule == 0
    cells, total = adaptive(A0, B0, granule)
    print(f"D = {D}: cells {len(cells)}, nodes {total}, "
          f"max cell nodes {max(c[2] for c in cells)}")
    for (x, y, n) in cells:
        print(f"  [{x/Q:.7f}, {y/Q:.7f}]  ({x}, {y})  nodes {n}")
    json.dump({"D": D, "Q": Q, "S": S, "cells": [[c[0], c[1]] for c in cells]},
              open('scripts/cells-exact.json', 'w'))
