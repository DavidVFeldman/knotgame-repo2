"""Exact replica of the Lean checker of `RequestProject.TransversalityChecker`.

Every constant, rounding and recursion below matches the Lean definitions
verbatim (`Dep`, `Qn`, `Scn`, `deltaS`, `OFF`, `TCAP`, `SLA`, `SLB`, `cdiv`,
`BP`, `DS`, `DD`, `TAn`, `TBn`, `XGS`, `XPS`, `keep`, `expand`, `layer`,
`capOK`, `cellOK`).  It is used to *find* a decomposition of the window
[1/2, 667/1000] into cells that the search certifies; the certificate itself is
re-checked by the Lean kernel, so this script is a search aid, not part of the
proof.

Usage:  python3 scripts/bnb_lean.py            # rebuild the decomposition
        python3 scripts/bnb_lean.py --check    # re-run the stored cells
"""
import json
import sys

Dep = 48
Qn = 1024000000                # = 2^16 * 5^6
Scn = 10 ** 18
deltaS = 10 ** 15              # delta = 1/1000 at scale Scn
TCAP = 10 ** 23
SLA = 4 * (Dep + 1)
SLB = 4 * (Dep + 1) * (Dep + 1)
A0 = Qn // 2                   # 1/2
B0 = 667 * (Qn // 1000)        # 667/1000


def cdiv(x, d):
    return (x + d - 1) // d


def thresholds(an, bn):
    BP = [Scn]
    for i in range(Dep + 1):
        BP.append(cdiv(BP[i] * bn, Qn))
    DS = [0]
    for i in range(Dep + 1):
        DS.append(DS[i] + (i + 1) * BP[i])
    DD = [0]
    for i in range(Dep + 1):
        DD.append(DD[i] + (i + 1) * i * BP[max(i - 1, 0)])
    w = bn - an
    TA, TB = [], []
    for i in range(Dep + 1):
        TA.append(deltaS + cdiv(DS[i] * w, 2 * Qn)
                  + cdiv(BP[i + 1] * Qn, Qn - bn) + SLA)
        TB.append(deltaS + cdiv(DD[i] * w, 2 * Qn)
                  + cdiv((i + 1) * BP[i] * Qn * Qn, (Qn - bn) ** 2) + SLB)
    return TA, TB


def run_cell(an, bn, cap=200_000):
    """Return (certified?, nodes, capOK?) for the cell [an/Qn, bn/Qn]."""
    mn = (an + bn) // 2
    assert (an + bn) % 2 == 0
    TA, TB = thresholds(an, bn)
    capok = all(TA[i] <= TCAP and TB[i] <= TCAP for i in range(Dep + 1))
    XG = [Scn]
    for i in range(Dep):
        XG.append(XG[i] * mn // Qn)
    XP = [0] + [i * XG[i - 1] for i in range(1, Dep + 1)]
    nodes = 0
    layer = [(Scn, 0)] if (Scn <= TA[0] and TB[0] >= 0) else []
    for i in range(1, Dep + 1):
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
            return None, nodes, capok
        if not layer:
            return True, nodes, capok
    return (len(layer) == 0), nodes, capok


def adaptive(a, b, granule):
    todo = [(a, b)]
    cells = []
    total = 0
    while todo:
        x, y = todo.pop()
        ok, n, capok = run_cell(x, y)
        if ok and capok:
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
    if '--check' in sys.argv:
        data = json.load(open('scripts/cells-exact.json'))
        cells = [tuple(c) for c in data['cells']]
        assert cells[0][0] == A0 and cells[-1][1] == B0
        for k in range(len(cells) - 1):
            assert cells[k][1] == cells[k + 1][0]
        total = 0
        worst = 0
        for (x, y) in cells:
            ok, n, capok = run_cell(x, y)
            total += n
            worst = max(worst, n)
            print(f"  ({x}, {y})  certified {ok}  capOK {capok}  nodes {n}")
            assert ok and capok
        print(f"all {len(cells)} cells certified, {total} nodes, max {worst}")
    else:
        cells, total = adaptive(A0, B0, granule)
        print(f"cells {len(cells)}, nodes {total}, "
              f"max cell nodes {max(c[2] for c in cells)}")
        for (x, y, n) in cells:
            print(f"  [{x/Qn:.7f}, {y/Qn:.7f}]  ({x}, {y})  nodes {n}")
        json.dump({"Dep": Dep, "Qn": Qn, "Scn": Scn,
                   "cells": [[c[0], c[1]] for c in cells]},
                  open('scripts/cells-lean.json', 'w'))
