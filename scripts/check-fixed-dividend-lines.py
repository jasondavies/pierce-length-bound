#!/usr/bin/env python3
"""Exact algebra checks for the 18/61 candidate (SymPy 1.14.0).

Generic line identities and residual degrees are symbolic checks. The resultant
specializations are regression tests, not proofs of the general degree bound.
No lattice enumeration or curve-counting estimate is asserted by this script.
"""

from random import Random

import sympy as sp

x, t = sp.symbols("x t")
rho, u, v, rhop, up, vp = sp.symbols("rho u v rhop up vp")
a, b, c = sp.symbols("a b c")
DIRECTIONS = [(0, 1, 1, 0, 1), (0, 1, 1, 0, 0),
              (0, 0, 1, 1, 0), (0, 1, 0, 0, 1)]


def forms(nodes):
    gaps = [nodes[j + 1] - nodes[j] for j in range(4)]
    gaps.append(rhop * gaps[1] - up * gaps[2] - vp * gaps[3])
    nodes = [*nodes, nodes[4] + gaps[4]]
    row = [gaps[j] * (nodes[j] + nodes[j + 1]) + gaps[j + 1]
           for j in range(4)]
    gaps.append(rhop * row[1] - up * row[2] - vp * row[3]
                - gaps[4] * (nodes[4] + nodes[5]))
    coeffs = [rho, -rho - u, u - v, v - 1, 1]
    quadratic = sum(coeffs[j] * (nodes[j] ** 2 + gaps[j]) for j in range(5))
    norm = sum(coeffs[j] * (nodes[j] ** 3 + 3 * nodes[j] ** 2
               + 3 * nodes[j] * (1 + gaps[j]) + (1 + gaps[j]) ** 2
               + gaps[j + 1]) for j in range(5))
    return sp.expand(quadratic), sp.expand(norm)


def quartics(nodes, cc, ee):
    p = sum(cc[j] * sp.prod(x - nodes[k] for k in range(j)) for j in range(5))
    r = sum(ee[j] * sp.prod(x - nodes[k] for k in range(1, j + 1)) for j in range(5))
    return sp.expand(p), sp.expand(r)


def check_line_identities():
    d = (rho + u) * a - (u - v) * b - (v - 1) * c
    cases = [({v: 1 - rho}, -rho * c, 2),
             ({v: -rho}, (rho + u) * (b - a - 1), 1),
             ({u: 1}, (v - 1) * (c - b - 1), 1),
             ({u: 1 - rho}, (u - v) - (d - a), 2)]
    for direction, (substitution, obstruction, multiple) in zip(DIRECTIONS, cases):
        nodes = [offset + t * step for offset, step in zip([0, a, b, c, d], direction)]
        f, norm = forms(nodes)
        identity = (norm.coeff(t, 2) - obstruction - multiple * f.coeff(t, 1))
        assert sp.expand(identity.subs(substitution)) == 0
    print("Four generic quadratic-coefficient identities: passed")


def check_residual_degrees():
    offsets = [0, *sp.symbols("a1:5")]
    cc, ee = [*sp.symbols("c0:4"), 1], [*sp.symbols("e0:4"), 1]
    cases = [([1, 2], (1, 2, 0, 1)), ([1, 2], (1, 2, 0, 2)),
             ([1], (0, 2, 0, 2)), ([1], (1, 3, 0, 2))]
    for direction, (indices, expected) in zip(DIRECTIONS, cases):
        nodes = [offset + t * step for offset, step in zip(offsets, direction)]
        p, r = quartics(nodes, cc, ee)
        for j in indices:
            expressions = [p.subs(x, nodes[j]), sp.diff(p, x).subs(x, nodes[j]),
                           r.subs(x, nodes[j]), sp.diff(r, x).subs(x, nodes[j])]
            degrees = tuple(sp.degree(sp.expand(expr), t) for expr in expressions)
            assert degrees == expected, (direction, j, degrees, expected)
    print("Six generic shared-node residual/derivative degree checks: passed")


def check_resultant_specializations():
    rng = Random(1861)
    seen = []
    for direction in DIRECTIONS:
        degrees = []
        for _ in range(6):
            offsets = [0, *rng.sample(range(-12, 13), 4)]
            cc = [rng.randint(-5, 5) for _ in range(4)] + [1]
            ee = [rng.randint(-5, 5) for _ in range(4)] + [1]
            nodes = [offset + t * step for offset, step in zip(offsets, direction)]
            p, r = quartics(nodes, cc, ee)
            resultant = sp.resultant(p, x * r, x)
            assert sp.expand(resultant - cc[0] * sp.resultant(p, r, x)) == 0
            degree = sp.degree(resultant, t)
            assert degree <= 6, (direction, degree)
            degrees.append(degree)
        seen.append(max(degrees))
    assert seen == [6, 6, 6, 6], seen
    print("24 exact resultant degree/normalization specializations: passed (maxima 6,6,6,6)")


if __name__ == "__main__":
    check_line_identities()
    check_residual_degrees()
    check_resultant_specializations()
