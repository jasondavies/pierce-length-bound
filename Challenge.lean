/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib

/-!
# Bounds for the iteration `x ↦ a mod x`

For natural numbers `0 < b < a`, repeatedly replace the positive remainder `x` by
`a % x`, stopping at zero. `P a b` counts the positive terms, including `b`.
The strongest result here is the uniform bound `P(a,b) ≪_ε a^(45/152 + ε)`.
The four earlier exponents are included to cover the results advertised in the paper.
The conjectured `O((log a)^2)` bound remains open.

Two further results give a conditional logarithmic refinement and a bound in terms
of rises in the quotient increments. The final theorem states positivity and
integrality of the entire Hankel hierarchy of the orbit's exact moment model.

All mathematical definitions below are supplied in full. Only the eight theorem
proofs have deliberate holes. In particular, the two analytic inputs are explicit
propositions, not axioms: their proofs are outside this formalization. All constants
in the length bounds are uniform in `a` and `b`.
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- One remainder step, frozen at zero after termination. -/
def step (a x : ℕ) : ℕ := if x = 0 then 0 else a % x

/-- The zero-indexed orbit; `orb a b 0 = b`. -/
def orb (a b : ℕ) (i : ℕ) : ℕ := (step a)^[i] b

/-- The number of positive terms before the orbit reaches zero. -/
def P (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | b + 1 => P a (a % (b + 1)) + 1
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

/-- The main unconditional bound, with an arbitrary positive exponent loss. -/
theorem P_le_45_152 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((45 : ℝ) / 152 + ε) := by
  sorry

/-- The earlier bound obtained by counting minor vectors. -/
theorem P_le_8_27 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((8 : ℝ) / 27 + ε) := by
  sorry

/-- The earlier bound obtained by slicing the pattern quadric. -/
theorem P_le_11_37 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((11 : ℝ) / 37 + ε) := by
  sorry

/-- The earlier bound obtained by counting seven-integer patterns. -/
theorem P_le_23_77 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((23 : ℝ) / 77 + ε) := by
  sorry

/-- The unconditional `3/10` bound, proved using the six-step identity. -/
theorem P_le : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((3 : ℝ) / 10 + ε) := by
  sorry

/-- The number of positive divisors of `n` in `(exp u, exp (u+1)]`. -/
noncomputable def hooleyCount (n : ℕ) (u : ℝ) : ℕ :=
  (n.divisors.filter fun d : ℕ => Real.exp u < (d : ℝ) ∧ (d : ℝ) ≤ Real.exp (u + 1)).card

/-- The Erdős–Hooley function: the maximum number of divisors in such an interval. -/
noncomputable def hooleyDelta (n : ℕ) : ℕ := ⨆ u : ℝ, hooleyCount n u

/-- The short-sum consequence of Nair–Tenenbaum (1998), Theorem 1, specialized
to `F = Δ`, `Q(X) = X`, and interval exponent `1/4`. Its proof is not formalized. -/
def NairTenenbaumDelta : Prop :=
  ∃ C x₀ : ℝ, ∀ x y : ℕ, x₀ ≤ x → (x : ℝ) ^ (1 / 4 : ℝ) ≤ y → y ≤ x →
    ∑ n ∈ Ioc x (x + y), (hooleyDelta n : ℝ) ≤
      C * (y / Real.log x) * ∑ n ∈ Icc 1 x, (hooleyDelta n : ℝ) / n

/-- The mean-value bound of de la Bretèche–Tenenbaum (2025), Theorem 1.1.
Its proof is not formalized. -/
def BretecheTenenbaumMean : Prop :=
  ∃ C x₀ : ℝ, ∀ x : ℕ, x₀ ≤ x →
    ∑ n ∈ Icc 1 x, (hooleyDelta n : ℝ) ≤ C * x * Real.log (Real.log x) ^ (5 / 2 : ℝ)

/-- Assuming the two displayed analytic statements, the `3/10` bound has only
a `sqrt(log(log(3a)))` loss. This theorem is conditional on both hypotheses. -/
theorem P_le_loglog (hNT : NairTenenbaumDelta) (hBT : BretecheTenenbaumMean) :
    ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (3 / 10 : ℝ) * √(Real.log (Real.log (3 * a))) := by
  sorry

/-- The increment between consecutive integer quotients along the orbit. -/
def incrO (a b i : ℕ) : ℕ := a / orb a b (i + 1) - a / orb a b i

/-- The number of strict rises between adjacent quotient increments.
The truncated range excludes increments involving the terminal zero. -/
def rises (a b : ℕ) : ℕ := ((range (P a b - 2)).filter
    fun i => incrO a b i < incrO a b (i + 1)).card

/-- A trajectory with `R - 1` rises has length `O(a^(1/4) sqrt R)`.
In particular, nonincreasing quotient increments give `O(a^(1/4))`. -/
theorem P_le_rises : ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ (1 / 4 : ℝ) * √(rises a b + 1) := by
  sorry

section Moments

variable (a b : ℕ)

/-- The quotient at the `i`th orbit term. -/
def qq (i : ℕ) : ℕ := a / orb a b i

/-- The support point given by the difference of two quotients, as a real number. -/
noncomputable def pt (i j : ℕ) : ℝ := (qq a b (i + j) : ℝ) - qq a b i

/-- The moment model's weights, defined backwards from unit mass at zero
at the last positive orbit term. Only indices `j < P a b - i` enter the moments. -/
noncomputable def wt (i : ℕ) : ℕ → ℝ :=
  if _h : i + 1 < P a b then
    fun j => if j = 0 then 1 - ∑ j' ∈ range (P a b - (i + 1)), wt (i + 1) j' / pt a b i (j' + 1)
      else wt (i + 1) (j - 1) / pt a b i j
  else fun j => if j = 0 then 1 else 0
termination_by P a b - i

/-- Moment of order `s`, with weight `wt(i,j) / q_(i+j)` at support point `pt(i,j)`. -/
noncomputable def hm (i s : ℕ) : ℝ :=
  ∑ j ∈ range (P a b - i), wt a b i j * pt a b i j ^ s / qq a b (i + j)

/-- The `r` by `r` Hankel matrix of these moments. -/
noncomputable def hankel (i r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun j l => hm a b i (j + l)

/-- The Hankel invariant: `a` times the determinant of the moment matrix. -/
noncomputable def hankelInv (i r : ℕ) : ℝ := a * (hankel a b i r).det

end Moments

/-- Every Hankel invariant up to the remaining orbit length is a positive integer.
The statement also includes `r = 0`, when the empty determinant is one. -/
theorem hankelInv_pos_int {a b : ℕ} (hba : b < a) {i r : ℕ}
    (hi : i < P a b) (hr : r ≤ P a b - i) :
    ∃ n : ℕ, 0 < n ∧ hankelInv a b i r = n := by
  sorry

end PierceLengthBound
