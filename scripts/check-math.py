#!/usr/bin/env python3
"""Independent exact-arithmetic checks of the paper; not a substitute for Lean.

Uses only the Python standard library. Checks every orbit with a <= 64,
256 seeded larger examples, and the two boundary/examples printed in the paper.
Hankel determinants are checked through order six, including terminal states.
"""

from collections import Counter
from fractions import Fraction as Q
from itertools import combinations
from random import Random


def determinant(rows):
    a = [list(map(Q, row)) for row in rows]
    result = Q(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return Q(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result
        p = a[j][j]
        result *= p
        for i in range(j + 1, len(a)):
            c = a[i][j] / p
            for k in range(j + 1, len(a)):
                a[i][k] -= c * a[j][k]
    return result


def orbit(a, b):
    values = []
    while b:
        values.append(b)
        b = a % b
    return values


def six_l(k, d):
    u, v, w, z = k[:4]
    f0, f1, f2 = d[:3]
    return ((v*w + w*w + z)*(f0*v - f1*u)
            - (u*u + (u-1)*v)*(f1*w - f2*v) - w*(w*f0-u*f2))


def six_s(u, v, w):
    return u*u*v + (u-1)*v*v + u*w


def six_j(u, v, w, z):
    return ((u*u + (u-1)*v)*z + w*(u**3 + u*v*(2*u-1) + (u-1)*v*v)
            + w*w*((u-1)*(u+v)+1))


def check_orbit(a, b, counts):
    bs = orbit(a, b)
    n = len(bs)
    qs = [a // x for x in bs]
    ks = [qs[i+1]-qs[i] for i in range(n-1)]
    ds = [bs[i]-(bs+[0])[i+1] for i in range(n)]
    assert all(k > 0 for k in ks)
    weights = [None] * n
    weights[-1] = [Q(1)]
    for i in range(n-2, -1, -1):
        tail = [w / (qs[i+j+1]-qs[i]) for j, w in enumerate(weights[i+1])]
        weights[i] = [1-sum(tail), *tail]

    hankels = {}
    for i in range(n):
        w = weights[i]
        assert all(t > 0 for t in w) and sum(w) == 1
        pts = [q-qs[i] for q in qs[i:]]
        h = [sum((w[j]*pts[j]**s/qs[i+j] for j in range(n-i)), Q(0))
             for s in range(2*min(6, n-i)-1)]
        assert h[0] == Q(bs[i], a)
        for s, value in enumerate(h):
            assert (value-(-qs[i])**s*Q(bs[i], a)).denominator == 1
        for r in range(1, min(6, n-i)+1):
            value = a*determinant([[h[j+l] for l in range(r)] for j in range(r)])
            assert value > 0 and value.denominator == 1, (a, b, i, r, value)
            hankels[i, r] = value
            counts['Hankel determinants'] += 1
        assert hankels[i, 1] == bs[i]
        if i+1 < n:
            assert hankels[i, 2] == ds[i]
        if i+3 < n:
            assert hankels[i, 3] == ds[i]*ks[i+1]-ds[i+1]*ks[i]
        if i+5 < n:
            assert hankels[i, 4] == six_l(ks[i:], ds[i:])

    for i in range(n-2):
        u, v = ks[i:i+2]
        d, e, f = ds[i:i+3]
        D = d*v-e*u
        assert D > 0 and D*bs[i+2] == d*f+u*d*e+(u-1)*e*e
        q = qs[i]
        assert bs[i]*(u*q*q+(u*u+u+v)*q+v) == a*(u*q+u*u+v)+D
        counts['curvature/fiber blocks'] += 1
    for i in range(n-4):
        u, v, w, z = ks[i:i+4]
        L = six_l(ks[i:], ds[i:])
        D, E, F = [ds[j]*ks[j+1]-ds[j+1]*ks[j] for j in range(i, i+3)]
        assert L > 0 and v*L == six_s(v,w,z)*D-six_s(u,v,w)*E
        assert qs[i]*w*L == six_j(u,v,w,z)*E+six_s(u,v,w)*F
        counts['six-step blocks'] += 1

    for i in range(n-8):
        k = ks[i:i+7]
        d = ds[i:i+5]
        ss = [sum(k[:j]) for j in range(6)]
        rr = [k[j]*(ss[j]+ss[j+1])+k[j+1] for j in range(5)]
        p = {cols: determinant([[row[j] for j in cols] for row in (d, k, rr)])
             for cols in combinations(range(5), 3)}
        A, B, C, U, V, Up, Vp = (p[0,1,2], p[1,2,3], p[2,3,4],
                                   p[0,2,3], -p[0,1,3], p[1,3,4], -p[1,2,4])
        assert (A, B, C) == tuple(hankels[i+j, 4] for j in range(3))
        assert U > 0 > V
        assert B*k[0] == U*k[1]+V*k[2]+A*k[3]
        assert B*k[4] == C*k[1]-Up*k[2]-Vp*k[3]
        x, y, z = k[1:4]
        F = ((U*x+V*y+A*z)**2+B*U*x*x+B*V*y*y+A*B*z*z
             +2*B*V*x*y+2*A*B*x*z+2*A*B*y*z
             +(A*C-B*B)*x+(B*U-A*Up)*y+(B*V-A*Vp)*z)
        assert F == 0
        coeffs = [-B, U, V, A]
        newton, quartic = 1, 0
        for j in range(4):
            quartic += coeffs[j]*newton*(-qs[i]-ss[j]-1)
            newton *= -qs[i]-ss[j]
        mu = [sum((weights[i][j]*(qs[i+j]-qs[i])**s for j in range(n-i)), Q(0))
              for s in range(7)]
        assert quartic == a*determinant([[mu[j+l] for l in range(4)] for j in range(4)])
        window_a, H = bs[i]//2+1, max(k)
        assert all(abs(v)*a**3 <= 3609600*window_a**4*H**6 for v in p.values())
        counts['pattern/quadric/quartic/minor blocks'] += 1
    counts['orbits'] += 1
    return hankels


def main():
    counts = Counter()
    samples = {(a, b) for a in range(2, 65) for b in range(1, a)}
    rng = Random(45152)
    for _ in range(256):
        a = rng.randrange(65, 10**6)
        samples.add((a, rng.randrange(1, a)))
    samples.update([(926, 229), (13242, 255)])
    for a, b in sorted(samples):
        h = check_orbit(a, b, counts)
        if (a, b) == (926, 229):
            assert h[1, 3] == 984  # Not the terminal curvature 988.
    assert orbit(35, 22) == [22, 13, 9, 8, 3, 2, 1]
    assert orbit(13242, 255)[:8] == [255, 237, 207, 201, 177, 144, 138, 132]
    assert Q(45,152) < Q(8,27) < Q(11,37) < Q(23,77) < Q(3,10)
    for name, count in sorted(counts.items()):
        print(f'{name}: {count}')
    print('Exact-arithmetic checks passed (finite checks, not a proof of the asymptotic bounds).')


if __name__ == '__main__':
    main()
