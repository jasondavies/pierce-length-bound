/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceBound.SixStep

/-!
# The two-state pattern: exact algebra

At a state with drops `d₀,…,d₃` and quotient increments `k₀,…,k₄` put `sₘ = k₀ + ⋯ + k_{m-1}`
and `rₘ = kₘ(sₘ + sₘ₊₁) + kₘ₊₁`. The `3 × 4` integer matrix with rows `(dₘ)`, `(kₘ)`, `(rₘ)` has the
cofactor null vector `(U₀, U₁, U₂, U₃)`, where

* `U₃ = det(columns 0,1,2) = L(i)` is the six-step integer `sixL` (equal to `I₄(i)`);
* `U₀ = -det(columns 1,2,3) = -L(i+1)`;
* `U₁ = pU1`, `U₂ = pU2`.

The null-vector relations `∑ Uₘ dₘ = ∑ Uₘ kₘ = ∑ Uₘ rₘ = 0` are polynomial identities
(`null_d`, `null_k`, `null_r`). The last two give the two counting facts:

* `quad_root`: if two states share `(U(i), U(i+1))`, the linear relations at `i` and `i+1`
  eliminate `k₀` and `k₄`, and the quadratic relation at `i` becomes
  `α k₃² + β k₃ + γ = 0` with `α = L(i) L(i+1) (L(i) + L(i+1)) > 0`;
* `mult_identity`: `∑ₘ Uₘ Fₘ(-q)(-q - sₘ - 1) = a · H₄(k₀,…,k₄)`, modulo the division relations
  `(q + sₘ) bₘ + bₘ₊₁ = a`. Here `Fₘ(x) = ∏_{l<m} (x - s_l)` and `H₄` is the Hankel determinant of
  the moments of `μᵢ`. This is `I₄(i) pᵢ(-qᵢ) = a H₄(i)` for the orthogonal polynomial `pᵢ`, and is
  a quartic equation for `qᵢ` with leading coefficient `U₃`.
-/

@[expose] public section

namespace PierceBound

open Finset Polynomial

/-- The cofactor `U₁`. -/
def pU1 (d0 d2 d3 k0 k1 k2 k3 k4 : ℤ) : ℤ :=
  d0*k2^2*k3 + d0*k2*k3^2 + d0*k2*k4 - d0*k3^2 - d2*k0^2*k3 - 2*d2*k0*k1*k3 - 2*d2*k0*k2*k3
      - d2*k0*k3^2 - d2*k0*k4 + d2*k1*k3 + d3*k0^2*k2 + 2*d3*k0*k1*k2 + d3*k0*k2^2 + d3*k0*k3
      - d3*k1*k2

/-- The cofactor `U₂`. -/
def pU2 (d0 d1 d3 k0 k1 k2 k3 k4 : ℤ) : ℤ :=
  -d0*k1^2*k3 - 2*d0*k1*k2*k3 - d0*k1*k3^2 - d0*k1*k4 + d0*k2*k3 + d1*k0^2*k3 + 2*d1*k0*k1*k3
      + 2*d1*k0*k2*k3 + d1*k0*k3^2 + d1*k0*k4 - d1*k1*k3 - d3*k0^2*k1 - d3*k0*k1^2 - d3*k0*k2
      + d3*k1^2

/-- **The null-vector relation for the drops** `∑ Uₘ dₘ = 0`. -/
theorem null_d (d0 d1 d2 d3 k0 k1 k2 k3 k4 : ℤ) :
    -sixL k1 k2 k3 k4 d1 d2 d3 * d0 + pU1 d0 d2 d3 k0 k1 k2 k3 k4 * d1 +
      pU2 d0 d1 d3 k0 k1 k2 k3 k4 * d2 + sixL k0 k1 k2 k3 d0 d1 d2 * d3 = 0 := by
  unfold sixL pU1 pU2; ring

/-- **The null-vector relation for the increments** `∑ Uₘ kₘ = 0`. -/
theorem null_k (d0 d1 d2 d3 k0 k1 k2 k3 k4 : ℤ) :
    -sixL k1 k2 k3 k4 d1 d2 d3 * k0 + pU1 d0 d2 d3 k0 k1 k2 k3 k4 * k1 +
      pU2 d0 d1 d3 k0 k1 k2 k3 k4 * k2 + sixL k0 k1 k2 k3 d0 d1 d2 * k3 = 0 := by
  unfold sixL pU1 pU2; ring

/-- **The null-vector relation for the quadratic row** `∑ Uₘ rₘ = 0`. -/
theorem null_r (d0 d1 d2 d3 k0 k1 k2 k3 k4 : ℤ) :
    -sixL k1 k2 k3 k4 d1 d2 d3 * (k0 ^ 2 + k1) +
      pU1 d0 d2 d3 k0 k1 k2 k3 k4 * (k1 * (2 * k0 + k1) + k2) +
      pU2 d0 d1 d3 k0 k1 k2 k3 k4 * (k2 * (2 * k0 + 2 * k1 + k2) + k3) +
      sixL k0 k1 k2 k3 d0 d1 d2 * (k3 * (2 * k0 + 2 * k1 + 2 * k2 + k3) + k4) = 0 := by
  unfold sixL pU1 pU2; ring

/-! ### The quadratic count -/

/-- The linear coefficient of the reduced quadratic. -/
def qB (Nn N1 _N2 u1 u2 _v1 v2 k1 k2 : ℤ) : ℤ :=
  2*N1^2*Nn*k1 + 2*N1^2*Nn*k2 + N1^2*u2 + 2*N1*Nn*u1*k1 + 2*N1*Nn*u2*k2 - N1*Nn*v2

/-- The constant term of the reduced quadratic. -/
def qC (Nn N1 N2 u1 u2 v1 _v2 k1 k2 : ℤ) : ℤ :=
  -N1^3*k1 + N1^2*u1*k1^2 + N1^2*u1*k2 + 2*N1^2*u2*k1*k2 + N1^2*u2*k2^2 + N1*N2*Nn*k1 - N1*Nn*v1*k2
      + N1*u1^2*k1^2 + 2*N1*u1*u2*k1*k2 + N1*u2^2*k2^2

/-- **The reduced quadratic.** Given the pattern `(Nn, N1, N2, u1, u2, v1, v2)`, i.e.
`U(i) = (-N1, u1, u2, Nn)` and `U(i+1) = (-N2, v1, v2, N1)`, eliminating `k₀` and `k₄` from the
quadratic relation at `i` leaves `N1 Nn (N1 + Nn) k₃² + β k₃ + γ = 0`. -/
theorem quad_root {Nn N1 N2 u1 u2 v1 v2 k0 k1 k2 k3 k4 : ℤ}
    (e0 : -N1 * k0 + u1 * k1 + u2 * k2 + Nn * k3 = 0)
    (e4 : -N2 * k1 + v1 * k2 + v2 * k3 + N1 * k4 = 0)
    (h : -N1 * (k0 ^ 2 + k1) + u1 * (k1 * (2 * k0 + k1) + k2) +
      u2 * (k2 * (2 * k0 + 2 * k1 + k2) + k3) +
      Nn * (k3 * (2 * k0 + 2 * k1 + 2 * k2 + k3) + k4) = 0) :
    N1 * Nn * (N1 + Nn) * k3 ^ 2 + qB Nn N1 N2 u1 u2 v1 v2 k1 k2 * k3 +
      qC Nn N1 N2 u1 u2 v1 v2 k1 k2 = 0 := by
  unfold qB qC
  linear_combination N1 ^ 2 * h - (N1*Nn) * e4 - (k0*N1^2 - N1*Nn*k3 - N1*u1*k1 - N1*u2*k2) * e0

/-! ### The quartic for the quotient -/

/-- `∑ₘ Uₘ Fₘ(Y) (Y - sₘ - 1)` evaluated at `Y = -q`. -/
def quart (U0 U1 U2 U3 k0 k1 k2 q : ℤ) : ℤ :=
  U0 * (-q - 1) + U1 * (-q) * (-q - k0 - 1) + U2 * (-q) * (-q - k0) * (-q - (k0 + k1) - 1) +
    U3 * (-q) * (-q - k0) * (-q - (k0 + k1)) * (-q - (k0 + k1 + k2) - 1)

/-- The rank-four Hankel determinant of the moments of `μᵢ`, as a polynomial in `k₀,…,k₄`. -/
def muH4 (k0 k1 k2 k3 k4 : ℤ) : ℤ :=
  k0^3*k1^2*k2 + k0^3*k1*k2^2 + k0^3*k1*k3 - k0^3*k2^2 + 2*k0^2*k1^3*k2 + 3*k0^2*k1^2*k2^2
      + 3*k0^2*k1^2*k3 + k0^2*k1*k2^3 - 2*k0^2*k1*k2^2 + 3*k0^2*k1*k2*k3 + k0^2*k1*k3^2 + k0^2*k1*k4
      - k0^2*k2^3 - k0^2*k2*k3 + k0*k1^4*k2 + 2*k0*k1^3*k2^2 - k0*k1^3*k2 + 2*k0*k1^3*k3
      + k0*k1^2*k2^3 - 3*k0*k1^2*k2^2 + 3*k0*k1^2*k2*k3 + k0*k1^2*k3^2 - k0*k1^2*k3 + k0*k1^2*k4
      - 2*k0*k1*k2^3 + k0*k1*k2^2 - 2*k0*k1*k2*k3 + k0*k2^3 + k0*k2^2*k3 + k0*k2*k3^2 + k0*k2*k4
      - k0*k3^2 - k1^4*k2 - 2*k1^3*k2^2 - 2*k1^3*k3 - k1^2*k2^3 + 2*k1^2*k2^2 - 3*k1^2*k2*k3
      - k1^2*k3^2 - k1^2*k4 + 2*k1*k2^3 + 2*k1*k2*k3 - k2^3

/-- **The multiplicity identity** `I₄(i) pᵢ(-qᵢ) = a H₄(i)`, modulo the division relations. -/
theorem mult_identity (a q b0 b1 b2 b3 b4 k0 k1 k2 k3 k4 : ℤ)
    (f0 : q * b0 + b1 = a) (f1 : (q + k0) * b1 + b2 = a) (f2 : (q + (k0 + k1)) * b2 + b3 = a)
    (f3 : (q + (k0 + k1 + k2)) * b3 + b4 = a) :
    quart (-sixL k1 k2 k3 k4 (b1 - b2) (b2 - b3) (b3 - b4))
        (pU1 (b0 - b1) (b2 - b3) (b3 - b4) k0 k1 k2 k3 k4)
        (pU2 (b0 - b1) (b1 - b2) (b3 - b4) k0 k1 k2 k3 k4)
        (sixL k0 k1 k2 k3 (b0 - b1) (b1 - b2) (b2 - b3)) k0 k1 k2 q =
      a * muH4 k0 k1 k2 k3 k4 := by
  unfold quart sixL pU1 pU2 muH4
  linear_combination (k0^3*k1^2*k2 + k0^3*k1*k2^2 + k0^3*k1*k3 - k0^3*k2^2 + 2*k0^2*k1^3*k2
      + 3*k0^2*k1^2*k2^2 + 3*k0^2*k1^2*k2*q + k0^2*k1^2*k2 + 3*k0^2*k1^2*k3 + k0^2*k1*k2^3
      + 3*k0^2*k1*k2^2*q - k0^2*k1*k2^2 + 3*k0^2*k1*k2*k3 + k0^2*k1*k3^2 + 3*k0^2*k1*k3*q
      + k0^2*k1*k3 + k0^2*k1*k4 - k0^2*k2^3 - 3*k0^2*k2^2*q - k0^2*k2^2 - k0^2*k2*k3 + k0*k1^4*k2
      + 2*k0*k1^3*k2^2 + 4*k0*k1^3*k2*q + k0*k1^3*k2 + 2*k0*k1^3*k3 + k0*k1^2*k2^3
      + 6*k0*k1^2*k2^2*q + 3*k0*k1^2*k2*k3 + 3*k0*k1^2*k2*q^2 + 2*k0*k1^2*k2*q + k0*k1^2*k3^2
      + 6*k0*k1^2*k3*q + 2*k0*k1^2*k3 + k0*k1^2*k4 + 2*k0*k1*k2^3*q - k0*k1*k2^3 + 3*k0*k1*k2^2*q^2
      - 2*k0*k1*k2^2*q - k0*k1*k2^2 + 6*k0*k1*k2*k3*q + k0*k1*k2*k3 + 2*k0*k1*k3^2*q + k0*k1*k3^2
      + 3*k0*k1*k3*q^2 + 2*k0*k1*k3*q + 2*k0*k1*k4*q + k0*k1*k4 - 2*k0*k2^3*q + k0*k2^2*k3
      - 3*k0*k2^2*q^2 - 2*k0*k2^2*q + k0*k2*k3^2 - 2*k0*k2*k3*q - k0*k2*k3 + k0*k2*k4 - k0*k3^2
      + k1^4*k2*q + 2*k1^3*k2^2*q + 2*k1^3*k2*q^2 + k1^3*k2*q + 2*k1^3*k3*q + k1^2*k2^3*q
      + 3*k1^2*k2^2*q^2 + 3*k1^2*k2*k3*q + k1^2*k2*q^3 + k1^2*k2*q^2 + k1^2*k3^2*q + 3*k1^2*k3*q^2
      + 2*k1^2*k3*q + k1^2*k4*q + k1*k2^3*q^2 - k1*k2^3*q + k1*k2^2*q^3 - k1*k2^2*q^2 - k1*k2^2*q
      + 3*k1*k2*k3*q^2 + k1*k2*k3*q + k1*k3^2*q^2 + k1*k3^2*q + k1*k3*q^3 + k1*k3*q^2 + k1*k4*q^2
      + k1*k4*q - k2^3*q^2 + k2^2*k3*q + k2^2*k3 - k2^2*q^3 - k2^2*q^2 + k2*k3^2*q + k2*k3^2
      - k2*k3*q^2 - k2*k3*q + k2*k4*q + k2*k4 - k3^2*q - k3^2) * f0
      + (-k0^4*k2*q - 4*k0^3*k1*k2*q - 2*k0^3*k2^2*q - 2*k0^3*k2*q^2 - k0^3*k2*q - 2*k0^3*k3*q
      - 6*k0^2*k1^2*k2*q - k0^2*k1^2*k2 - 6*k0^2*k1*k2^2*q - k0^2*k1*k2^2 - 6*k0^2*k1*k2*q^2
      - 2*k0^2*k1*k2*q - 6*k0^2*k1*k3*q - k0^2*k1*k3 - k0^2*k2^3*q - 3*k0^2*k2^2*q^2 + k0^2*k2^2
      - 3*k0^2*k2*k3*q - k0^2*k2*q^3 - k0^2*k2*q^2 - k0^2*k3^2*q - 3*k0^2*k3*q^2 - 2*k0^2*k3*q
      - k0^2*k4*q - 4*k0*k1^3*k2*q - 2*k0*k1^3*k2 - 6*k0*k1^2*k2^2*q - 3*k0*k1^2*k2^2
      - 6*k0*k1^2*k2*q^2 - 3*k0*k1^2*k2*q - k0*k1^2*k2 - 6*k0*k1^2*k3*q - 3*k0*k1^2*k3
      - 2*k0*k1*k2^3*q - k0*k1*k2^3 - 6*k0*k1*k2^2*q^2 - k0*k1*k2^2*q + k0*k1*k2^2 - 6*k0*k1*k2*k3*q
      - 3*k0*k1*k2*k3 - 2*k0*k1*k2*q^3 + k0*k1*k2*q - 2*k0*k1*k3^2*q - k0*k1*k3^2 - 6*k0*k1*k3*q^2
      - 5*k0*k1*k3*q - k0*k1*k3 - 2*k0*k1*k4*q - k0*k1*k4 - k0*k2^3*q^2 + k0*k2^3*q + k0*k2^3
      - k0*k2^2*q^3 + k0*k2^2*q^2 + 3*k0*k2^2*q + k0*k2^2 - 3*k0*k2*k3*q^2 - k0*k2*k3*q + k0*k2*k3
      - k0*k3^2*q^2 - k0*k3^2*q - k0*k3*q^3 - k0*k3*q^2 - k0*k4*q^2 - k0*k4*q - k1^4*k2*q - k1^4*k2
      - 2*k1^3*k2^2*q - 2*k1^3*k2^2 - 2*k1^3*k2*q^2 - 2*k1^3*k2*q - k1^3*k2 - 2*k1^3*k3*q
      - 2*k1^3*k3 - k1^2*k2^3*q - k1^2*k2^3 - 3*k1^2*k2^2*q^2 - 2*k1^2*k2^2*q - 3*k1^2*k2*k3*q
      - 3*k1^2*k2*k3 - k1^2*k2*q^3 - k1^2*k3^2*q - k1^2*k3^2 - 3*k1^2*k3*q^2 - 4*k1^2*k3*q
      - 2*k1^2*k3 - k1^2*k4*q - k1^2*k4 - k1*k2^3*q^2 + k1*k2^3 - k1*k2^2*q^3 + k1*k2^2*q^2
      + 2*k1*k2^2*q + k1*k2^2 - 3*k1*k2*k3*q^2 - 4*k1*k2*k3*q - k1*k2*k3 + k1*k2*q^3 + k1*k2*q^2
      - k1*k3^2*q^2 - 2*k1*k3^2*q - k1*k3^2 - k1*k3*q^3 - k1*k3*q^2 - k1*k4*q^2 - 2*k1*k4*q - k1*k4
      + k2^3*q^2 + k2^3*q - k2^2*k3*q - k2^2*k3 + k2^2*q^3 + 2*k2^2*q^2 + k2^2*q - k2*k3^2*q
      - k2*k3^2 + k2*k3*q^2 + 2*k2*k3*q + k2*k3 - k2*k4*q - k2*k4 + k3^2*q + k3^2) * f1
      + (k0^4*k1*q + k0^4*k2*q + 2*k0^3*k1^2*q + 4*k0^3*k1*k2*q + 2*k0^3*k1*q^2 + k0^3*k1*q
      + 2*k0^3*k2^2*q + 2*k0^3*k2*q^2 + 3*k0^3*k2*q + 2*k0^3*k3*q + k0^2*k1^3*q + 3*k0^2*k1^2*k2*q
      + 3*k0^2*k1^2*q^2 + 3*k0^2*k1*k2^2*q + 6*k0^2*k1*k2*q^2 + 5*k0^2*k1*k2*q + 3*k0^2*k1*k3*q
      + k0^2*k1*q^3 + k0^2*k1*q^2 + k0^2*k2^3*q + 3*k0^2*k2^2*q^2 + 4*k0^2*k2^2*q + 3*k0^2*k2*k3*q
      + k0^2*k2*q^3 + 4*k0^2*k2*q^2 + 2*k0^2*k2*q + k0^2*k3^2*q + 3*k0^2*k3*q^2 + 3*k0^2*k3*q
      + k0^2*k4*q + k0*k1^3*q^2 - k0*k1^3*q + 3*k0*k1^2*k2*q^2 + k0*k1^2*k2*q + k0*k1^2*k2
      + k0*k1^2*q^3 - k0*k1^2*q^2 - k0*k1^2*q + 3*k0*k1*k2^2*q^2 + 3*k0*k1*k2^2*q + k0*k1*k2^2
      + 2*k0*k1*k2*q^3 + 3*k0*k1*k2*q^2 + 3*k0*k1*k3*q^2 + 3*k0*k1*k3*q + k0*k1*k3 + k0*k2^3*q^2
      + k0*k2^3*q + k0*k2^2*q^3 + 3*k0*k2^2*q^2 - k0*k2^2 + 3*k0*k2*k3*q^2 + 3*k0*k2*k3*q
      + k0*k2*q^3 + k0*k2*q^2 + k0*k3^2*q^2 + k0*k3^2*q + k0*k3*q^3 + 2*k0*k3*q^2 + k0*k3*q
      + k0*k4*q^2 + k0*k4*q + k1^3*k2*q + k1^3*k2 - k1^3*q^2 + 2*k1^2*k2^2*q + 2*k1^2*k2^2
      - k1^2*k2*q^2 + k1^2*k2*q + k1^2*k2 + 2*k1^2*k3*q + 2*k1^2*k3 - k1^2*q^3 - k1^2*q^2
      + k1*k2^3*q + k1*k2^3 + 3*k1*k2*k3*q + 3*k1*k2*k3 - k1*k2*q^3 - 2*k1*k2*q^2 - k1*k2*q
      + k1*k3^2*q + k1*k3^2 + k1*k3*q + k1*k3 + k1*k4*q + k1*k4 - k2^3*q - k2^3 - k2^2*q^2
      - 2*k2^2*q - k2^2 - k2*k3*q - k2*k3) * f2 + (-k0^4*k1*q - 2*k0^3*k1^2*q - 2*k0^3*k1*q^2
      - k0^3*k1*q - 2*k0^3*k2*q - k0^2*k1^3*q - 3*k0^2*k1^2*q^2 - 3*k0^2*k1*k2*q - k0^2*k1*q^3
      - k0^2*k1*q^2 - k0^2*k2^2*q - 3*k0^2*k2*q^2 - 2*k0^2*k2*q - k0^2*k3*q - k0*k1^3*q^2
      + k0*k1^3*q - k0*k1^2*q^3 + k0*k1^2*q^2 + k0*k1^2*q - 3*k0*k1*k2*q^2 - k0*k1*k2*q
      - k0*k2^2*q^2 - k0*k2^2*q - k0*k2*q^3 - k0*k2*q^2 - k0*k3*q^2 - k0*k3*q + k1^3*q^2 - k1^2*k2*q
      - k1^2*k2 + k1^2*q^3 + k1^2*q^2 - k1*k2^2*q - k1*k2^2 + k1*k2*q^2 + k1*k2*q - k1*k3*q - k1*k3
      + k2^2*q + k2^2) * f3

/-- The coefficients of `quart` as a polynomial in `q`. -/
def quartC (U0 U1 U2 U3 k0 k1 k2 : ℤ) : Fin 4 → ℤ := ![
  -U0,
  -U0 + U1*k0 + U1 - U2*k0^2 - U2*k0*k1 - U2*k0 + U3*k0^3 + 2*U3*k0^2*k1 + U3*k0^2*k2 + U3*k0^2
      + U3*k0*k1^2 + U3*k0*k1*k2 + U3*k0*k1,
  U1 - 2*U2*k0 - U2*k1 - U2 + 3*U3*k0^2 + 4*U3*k0*k1 + 2*U3*k0*k2 + 2*U3*k0 + U3*k1^2 + U3*k1*k2
      + U3*k1,
  -U2 + 3*U3*k0 + 2*U3*k1 + U3*k2 + U3]

lemma quart_eq (U0 U1 U2 U3 k0 k1 k2 q : ℤ) :
    quart U0 U1 U2 U3 k0 k1 k2 q = U3 * q ^ 4 + quartC U0 U1 U2 U3 k0 k1 k2 3 * q ^ 3 +
      quartC U0 U1 U2 U3 k0 k1 k2 2 * q ^ 2 + quartC U0 U1 U2 U3 k0 k1 k2 1 * q +
      quartC U0 U1 U2 U3 k0 k1 k2 0 := by
  simp only [quart, quartC, Matrix.cons_val]; ring

/-! ### Root counting -/

lemma card_le_natDegree_of_roots {s : Finset ℤ} {p : ℤ[X]} (hp : p ≠ 0)
    (h : ∀ z ∈ s, p.eval z = 0) : s.card ≤ p.natDegree := by
  classical
  have hsub : s ⊆ p.roots.toFinset := fun z hz => by
    rw [Multiset.mem_toFinset, mem_roots hp]; exact h z hz
  calc s.card ≤ p.roots.toFinset.card := card_le_card hsub
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p

/-- A quadratic with nonzero leading coefficient has at most two integer roots. -/
lemma card_le_two_of_quad {s : Finset ℤ} {α β γ : ℤ} (hα : α ≠ 0)
    (h : ∀ z ∈ s, α * z ^ 2 + β * z + γ = 0) : s.card ≤ 2 := by
  set p : ℤ[X] := C α * X ^ 2 + C β * X + C γ
  have hp : p ≠ 0 := by
    intro h0
    have := congrArg (fun f => f.coeff 2) h0
    simp only [p, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at this
    norm_num at this
    exact hα this
  refine (card_le_natDegree_of_roots hp fun z hz => ?_).trans natDegree_quadratic_le
  simpa [p] using h z hz

/-- A quartic with nonzero leading coefficient has at most four integer roots. -/
lemma card_le_four_of_quartic {s : Finset ℤ} {c4 c3 c2 c1 c0 : ℤ} (hc : c4 ≠ 0)
    (h : ∀ z ∈ s, c4 * z ^ 4 + c3 * z ^ 3 + c2 * z ^ 2 + c1 * z + c0 = 0) : s.card ≤ 4 := by
  set p : ℤ[X] := C c4 * X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0
  have hp : p ≠ 0 := by
    intro h0
    have := congrArg (fun f => f.coeff 4) h0
    simp only [p, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at this
    norm_num at this
    exact hc this
  have hdeg : p.natDegree ≤ 4 := by
    simp only [p]; compute_degree!
  refine (card_le_natDegree_of_roots hp fun z hz => ?_).trans hdeg
  simpa [p] using h z hz

end PierceBound
