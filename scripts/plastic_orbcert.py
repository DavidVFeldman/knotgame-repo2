#!/usr/bin/env python3
"""Generate the reachability certificate `orbCert` of
RequestProject/PlasticOrbitCount.lean: for every orbit index, its distance
from the index of 1/2 in the automaton of PlasticIndex.lean, together with a
move and a predecessor index realising that distance.

The transition tables are read from the Lean source, so the certificate is
generated from exactly the data the kernel checks it against.
"""
import re
import sys
import textwrap

SRC = "/workspace/request-project/RequestProject/PlasticIndex.lean"
HALF = 76

txt = open(SRC).read()
tabs = []
for name in ("tabL", "tabM", "tabR"):
    m = re.search(r"def " + name + r" : \u2115 := (\d+)", txt)
    T = int(m.group(1))
    tabs.append([(T >> (8 * i)) % 256 for i in range(153)])

dep = {HALF: (0, 0, 0)}
frontier = [HALF]
while frontier:
    nxt = []
    for j in frontier:
        for mi, tab in enumerate(tabs):
            v = tab[j]
            if v != 255 and v not in dep:
                dep[v] = (dep[j][0] + 1, mi, j)
                nxt.append(v)
    frontier = nxt

missing = [i for i in range(153) if i not in dep]
print("reached %d of 153; missing %s; max distance %d"
      % (len(dep), missing, max(d for d, _, _ in dep.values())), file=sys.stderr)

items = ["(%d,%d,%d)" % dep[i] for i in range(153)]
body = "[" + ", ".join(items) + "]"
print("def orbCert : List (\u2115 \u00d7 \u2115 \u00d7 \u2115) :=\n  " +
      "\n  ".join(textwrap.wrap(body, 94)))
