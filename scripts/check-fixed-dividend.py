#!/usr/bin/env python3
"""Exact checks for the 13/44 candidate; requires SymPy (tested with 1.14.0).

These are finite algebraic checks, not a proof of the uniform counting theorem.
All sampled starts retain at least sixteen future positive states. Run from any
working directory with: python3 /path/to/scripts/check-fixed-dividend.py
"""

import importlib.util
import sys
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from random import Random

import sympy as sp

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location(
    "arithmetic", Path(__file__).with_name("check-math.py")
)
arithmetic = importlib.util.module_from_spec(spec)
spec.loader.exec_module(arithmetic)
x, t = sp.symbols("x t")


def polynomials(labels, gaps):
    """Construct the two quartics and cubic norm from the candidate's formulas."""
    a0, a1, a2, u, v, up, vp = map(sp.Rational, labels)
    coefficients = [a1/a0, -(a1+u)/a0, (u-v)/a0, v/a0-1, sp.Integer(1)]
    shifted = [a2/a1, -(a2+up)/a1, (up-vp)/a1, vp/a1-1, sp.Integer(1)]
    nodes = [sum(gaps[:j]) for j in range(6)]
    newton = [sp.prod(x-nodes[v] for v in range(j)) for j in range(6)]
    quartic = sum(coefficients[j]*newton[j] for j in range(5))
    next_quintic = sum(shifted[j]*newton[j+1] for j in range(5))
    norm = sum(
        coefficients[j] * (
            nodes[j]**3 + 3*nodes[j]**2 + 3*nodes[j]*(1+gaps[j])
            + (1+gaps[j])**2 + gaps[j+1]
        )
        for j in range(5)
    )
    return sp.Poly(quartic, x), sp.Poly(next_quintic, x), sp.expand(norm), coefficients


def check_explicit_example():
    quartic, quintic, norm, _ = polynomials(
        [108, 24, 12, 156, -240, 48, -60], [t]*6
    )
    omega = sp.factor(108*sp.resultant(quartic, quintic, x) - 473*norm**4)
    expected = -sp.Rational(16, 81)*t**6*(t-1) * (
        1135673*t**5 + 1135673*t**4 + 446633*t**3
        + 97859*t**2 + 13518*t + 1080
    )
    assert sp.expand(omega-expected) == 0
    print("Explicit normalization polynomial: passed")


def check_orbit(dividend, initial, leading_checks):
    values = arithmetic.orbit(dividend, initial)
    quotients = [dividend // value for value in values]
    gaps = [quotients[j+1]-quotients[j] for j in range(len(quotients)-1)]
    weights = [None]*len(values)
    weights[-1] = [Fraction(1)]
    for i in range(len(values)-2, -1, -1):
        tail = [
            weight/(quotients[i+j+1]-quotients[i])
            for j, weight in enumerate(weights[i+1])
        ]
        weights[i] = [1-sum(tail), *tail]
        assert all(weight > 0 for weight in weights[i])
        assert sum(weights[i]) == 1

    checked = 0
    for i in range(len(values)-16):
        local_gaps = gaps[i:i+6]
        drops = [values[i+j]-values[i+j+1] for j in range(5)]
        nodes = [sum(local_gaps[:j]) for j in range(6)]
        quadratic_row = [
            local_gaps[j]*(nodes[j]+nodes[j+1])+local_gaps[j+1]
            for j in range(5)
        ]
        minors = {
            cols: arithmetic.determinant([
                [row[j] for j in cols] for row in (drops, local_gaps, quadratic_row)
            ])
            for cols in combinations(range(5), 3)
        }
        labels = [
            minors[0, 1, 2], minors[1, 2, 3], minors[2, 3, 4],
            minors[0, 2, 3], -minors[0, 1, 3], minors[1, 3, 4], -minors[1, 2, 4],
        ]
        quartic, quintic, norm, _ = polynomials(labels, local_gaps)

        def weighted_moment(poly):
            return sum(
                sp.Rational(weight)*poly.eval(quotients[i+j]-quotients[i])/quotients[i+j]
                for j, weight in enumerate(weights[i])
            )

        for j in range(4):
            monomial = sp.Poly(x**j, x)
            assert weighted_moment(quartic*monomial) == 0
            assert weighted_moment(quintic*monomial) == 0
        assert weighted_moment(quartic*quartic) == norm > 0
        resultant = sp.resultant(quartic, quintic, x)
        assert labels[0]*resultant == dividend*norm**4, (dividend, initial, i)

        raw = [
            sum(weight*(quotients[i+j]-quotients[i])**m
                for j, weight in enumerate(weights[i]))
            for m in range(7)
        ]
        raw_hankel = arithmetic.determinant([[raw[j+k] for k in range(4)] for j in range(4)])
        assert labels[0]*quartic.eval(-quotients[i]) == dividend*raw_hankel

        if leading_checks < 7:
            scaled_quartic, scaled_quintic, _, coefficients = polynomials(
                labels, [t*gap for gap in local_gaps]
            )
            scaled_resultant = sp.Poly(sp.resultant(scaled_quartic, scaled_quintic, x), t)
            expected_lead = sp.prod(coefficients[:4]) * sp.prod(
                nodes[l]-nodes[j] for j, l in combinations(range(5), 2)
            )
            assert scaled_resultant.degree() == 10
            assert scaled_resultant.LC() == expected_lead
            leading_checks += 1
        checked += 1
    return checked, leading_checks


def main():
    check_explicit_example()
    rng = Random(1344)
    checked = leading_checks = attempts = 0
    while checked < 200:
        dividend = rng.randrange(10000, 10**8)
        initial = rng.randrange(1, dividend)
        count, leading_checks = check_orbit(dividend, initial, leading_checks)
        checked += count
        attempts += 1
        if attempts > 100000:
            raise RuntimeError("Unable to obtain the required number of supported starts")
    print(f"Verified supported starts: {checked}")
    print(f"Degree-ten leading-form specializations: {leading_checks}")
    print("Finite exact checks passed; this is not a formal proof of 13/44.")


if __name__ == "__main__":
    main()
