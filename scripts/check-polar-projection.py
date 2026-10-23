#!/usr/bin/env python3
"""Exact symbolic checks for the polar identity and its two certificates.

Requires SymPy. These checks supplement the Lean proofs; they do not establish
local intersection multiplicities, the uniform branch sieve, or the six-term count.
The coefficient specialization is synthetic, not an asserted Pierce orbit state.
"""
from itertools import combinations

import sympy as s

rho, u, v, rp, up, vp = s.symbols("rho u v rp up vp")
x = s.Matrix(s.symbols("x0:3"))
xi, t1, t2, z = s.symbols("xi t1 t2 z")
parameters = (rho, u, v, rp, up, vp)
G = s.Matrix([
    [rho * (rho + 1), -rho * (u - 1), -rho * (v - 1)],
    [-rho * (u - 1), u * (u - 1), u * (v - 1)],
    [-rho * (v - 1), u * (v - 1), v * (v - 1)],
])
ell = s.Matrix([rho * (v - vp), rp - rho - u * (v - vp), u - up - v * (v - vp)])
c = [rho, -rho - u, u - v, v - 1, 1]
cp = [rp, -rp - up, up - vp, vp - 1, 1]
k = list(x) + [rho * x[0] - u * x[1] - v * x[2]]
k.append(rp * k[1] - up * k[2] - vp * k[3])
nodes = [sum(k[:j]) for j in range(6)]
r = [k[j] * (nodes[j] + nodes[j + 1]) + k[j + 1] for j in range(4)]
k.append(rp * r[1] - up * r[2] - vp * r[3] - k[4] * (nodes[4] + nodes[5]))
f = sum(c[j] * (nodes[j] ** 2 + k[j]) for j in range(5))
D = sum(c[j] * (nodes[j] ** 3 + 3 * nodes[j] ** 2
                + 3 * nodes[j] * (1 + k[j]) + (1 + k[j]) ** 2 + k[j + 1])
        for j in range(5))
V = G * x + ell
assert s.expand(f - (x.T * G * x)[0] - (ell.T * x)[0]) == 0
assert s.expand(G.det() - rho * (rho + u) * (u - v) * (v - 1)) == 0
assert s.expand(V.dot(s.Matrix(r[:3])) - D + (nodes[4] + 1 + v - vp) * f) == 0
print("Generic quadric, determinant and norm identities: PASS", flush=True)

star_nodes = [0] + [(cp[j - 1] - c[j - 1]) / c[j] for j in range(1, 4)] + [vp - v]
star = s.Matrix([star_nodes[j + 1] - star_nodes[j] for j in range(3)])
assert all(s.factor(entry) == 0 for entry in G * star + ell)
P = sum(c[j] * s.prod(xi - nodes[l] for l in range(j)) for j in range(5))
R = sum(cp[j] * s.prod(xi - nodes[l] for l in range(1, j + 1)) for j in range(5))
h = vp - v - nodes[4]
tcoef = [-h * c[0]] + [cp[j - 1] - c[j - 1] - c[j] * (nodes[j] + h)
                       for j in range(1, 4)]
remainder = sum(tcoef[j] * s.prod(xi - nodes[l] for l in range(j)) for j in range(4))
assert s.expand(xi * R - (xi + h) * P - remainder) == 0
print("Generic base point and Newton division: PASS", flush=True)

certificate = dict(zip(parameters, [2, 5, -3, 3, 6, -5]))
star_c = star.subs(certificate)
assert star_c == s.Matrix([-s.Rational(1, 7), -s.Rational(3, 28), -s.Rational(1, 2)])
M = s.Matrix([[1, 0, 0, 2, 10], [0, 1, 0, -5, -22], [0, 0, 1, 3, 9]])
minors = {idx: M[:, idx].det() for idx in combinations(range(5), 3)}
assert minors == {
    (0, 1, 2): 1, (0, 1, 3): 3, (0, 1, 4): 9, (0, 2, 3): 5, (0, 2, 4): 22,
    (0, 3, 4): 21, (1, 2, 3): 2, (1, 2, 4): 10, (1, 3, 4): 12, (2, 3, 4): 6,
}
tangent = s.Matrix([(9 * t1 - 5 * t2) / 4, t1, t2])
base = dict(zip(x, star_c))
displacement = dict(zip(x, star_c + z * tangent))
P_star = s.expand(P.subs(certificate).subs(base))
R1 = s.expand(remainder.subs(certificate).subs(displacement)).coeff(z, 1)
D1 = s.expand(D.subs(certificate).subs(displacement)).coeff(z, 1)
N4 = s.factor(s.resultant(P_star, R1, xi))
assert s.expand(P_star - (xi ** 4 - s.Rational(20, 7) * xi ** 3
                         + s.Rational(757, 112) * xi ** 2
                         - s.Rational(669, 112) * xi + 2)) == 0
assert s.expand(R1 - ((77 * t1 + 7 * t2) + (-56 * t1 - 124 * t2) * xi
                     + (-45 * t1 + 157 * t2) * xi ** 2
                     + (28 * t1 - 28 * t2) * xi ** 3) / 14) == 0
assert s.expand(D1 - (3 * t1 + 85 * t2) / 28) == 0
assert s.expand(N4 - (32233977 * t1 ** 4 - 95047956 * t1 ** 3 * t2
                     + 147873750 * t1 ** 2 * t2 ** 2 - 111199572 * t1 * t2 ** 3
                     + 31702169 * t2 ** 4) / 6272) == 0
np, dp = s.Poly(N4, t1, t2), s.Poly(D1 ** 4, t1, t2)
determinant = (np.coeff_monomial(t1 ** 4) * dp.coeff_monomial(t2 ** 4)
               - np.coeff_monomial(t2 ** 4) * dp.coeff_monomial(t1 ** 4))
assert determinant == s.Rational(26291112152499, 60236288)
print("Decomposable coefficient pattern and quartic certificate: PASS", flush=True)

E = s.Poly(2400 * xi ** 6 - 20160 * xi ** 5 + 69776 * xi ** 4 - 126448 * xi ** 3
           + 125636 * xi ** 2 - 64680 * xi + 13475, xi)
e71 = s.Poly(xi ** 6 + 20 * xi ** 5 - 14 * xi ** 4 + 15 * xi ** 3
             - 28 * xi ** 2 + 5 * xi - 4, xi, modulus=71)
assert E.set_modulus(71).monic() == e71
assert e71.is_irreducible
assert E.is_irreducible
print("Branch sextic irreducible modulo 71 and over Q: PASS", flush=True)

q = s.Rational
m, n = 3, 2
degree = 60 * n + 56 * m
exponents = [q(5, 17), q(45 * degree, 153 * degree - 1),
             q(45 * degree - 3 * m, 153 * degree - 11 * m),
             q(15 * degree + 6 * n, 51 * degree + 20 * n)]
assert degree == 288
assert max(exponents) == q(4317, 14677)
assert max(q(717, 2440), q(732, 2491)) < q(5, 17)
ratio = (s.sqrt(82849) - 47) / 360
beta = (41301 - 3 * s.sqrt(82849)) / 137480
assert s.simplify((2700 * ratio + 2517) / (9180 * ratio + 8557) - beta) == 0
assert s.simplify((906 * ratio + 840) / (3080 * ratio + 2856) - beta) == 0
assert q(5, 17) < beta < q(4317, 14677) < q(153, 520)
print("Rational and optimized polar exponents: PASS", flush=True)
