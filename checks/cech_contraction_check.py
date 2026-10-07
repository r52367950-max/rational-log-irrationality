"""Exact finite audit of the signed contraction in Theorem A, Lemma 5.1.

This verifies signs in dimensions 2 through 8; it is not a proof for all d.
"""
from itertools import combinations


def add(out, key, coefficient):
    out[key] = out.get(key, 0) + coefficient
    if out[key] == 0:
        del out[key]


def differential(chain, d, mandatory):
    out = {}
    for s, coefficient in chain.items():
        for vertex in range(d):
            if vertex not in s:
                target = tuple(sorted(s + (vertex,)))
                add(out, target, coefficient * (-1) ** target.index(vertex))
    return out


def contraction(chain, vertex, mandatory):
    out = {}
    for s, coefficient in chain.items():
        if vertex in s:
            target = tuple(x for x in s if x != vertex)
            if set(mandatory).issubset(target):
                add(out, target, coefficient * (-1) ** s.index(vertex))
    return out


checked = 0
for d in range(2, 9):
    vertices = set(range(d))
    for tsize in range(1, d):
        for mandatory in combinations(range(d), tsize):
            vertex = min(vertices - set(mandatory))
            for ssize in range(tsize, d + 1):
                for s in combinations(range(d), ssize):
                    if not set(mandatory).issubset(s):
                        continue
                    basis = {s: 1}
                    dh = differential(contraction(basis, vertex, mandatory), d, mandatory)
                    hd = contraction(differential(basis, d, mandatory), vertex, mandatory)
                    for target, coefficient in hd.items():
                        add(dh, target, coefficient)
                    assert dh == basis, (d, mandatory, s, dh)
                    checked += 1
print(f"Verified dh + hd = id on {checked} basis cochains for dimensions 2–8.")
