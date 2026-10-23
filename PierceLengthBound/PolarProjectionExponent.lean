/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LatticeJointWindow

/-!
# Exponent arithmetic for the polar-projection bound

The degree-24 component and curvature pullback degree 20 give the powered degree
`h = 60n + 56m`. This file checks the resulting exponents, including the exceptional-pattern
terms with exponent `14/3`, and the rational choice `m = 3`, `n = 2`.

This file isolates the arithmetic implications of the counting branches.
`PolarProjectionMain` supplies the arithmetic and geometric inputs and proves the length bounds.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The powered-graph degree when the original degree is 24 and the curvature
pullback degree is 20. -/
def polarProjectionGraphDegree (m n : ℕ) : ℕ := 60 * n + 56 * m

lemma polarProjectionGraphDegree_formula (m n : ℕ) :
    ((5 * n + 3 * m : ℕ) : ℝ) / 2 * 24 + 20 * m = polarProjectionGraphDegree m n := by
  unfold polarProjectionGraphDegree
  push_cast
  ring

/-- The maximum of the complementary-range exponent and the three good-pattern exponents. -/
def polarProjectionExponent (m n : ℕ) : ℝ :=
  max (max ((5 : ℝ) / 17) (latticeExponentH (polarProjectionGraphDegree m n)))
    (max (latticeExponentS (polarProjectionGraphDegree m n) m)
      (latticeExponentY (polarProjectionGraphDegree m n) n))

/-- The powers `m = 3`, `n = 2` give degree 288 and exponent 4317/14677. -/
theorem polarProjection_rational_example :
    polarProjectionGraphDegree 3 2 = 288 ∧
      latticeExponentH 288 = 12960 / 44063 ∧
      latticeExponentS 288 3 = 4317 / 14677 ∧
      latticeExponentY 288 2 = 1083 / 3682 ∧
      polarProjectionExponent 3 2 = 4317 / 14677 := by
  norm_num [polarProjectionGraphDegree, polarProjectionExponent,
    latticeExponentH, latticeExponentS, latticeExponentY]

/-- Enlarging the exceptional class to `X^(14/3)` still gives exponents strictly below
the complementary-range threshold `5/17`. -/
lemma polarProjection_bad_pattern_exponents :
    ((3 * 238 + 3 : ℕ) : ℝ) / (51 + 10 * 238 + 9 : ℕ) = 717 / 2440 ∧
      ((3 * 238 + 18 : ℕ) : ℝ) / (51 + 10 * 238 + 60 : ℕ) = 732 / 2491 ∧
      (5 : ℝ) / 17 - 717 / 2440 = 11 / 41480 ∧
      (5 : ℝ) / 17 - 732 / 2491 = 11 / 42347 := by
  norm_num

lemma polarProjection_rational_comparisons :
    (717 : ℝ) / 2440 < 5 / 17 ∧ (732 : ℝ) / 2491 < 5 / 17 ∧
      (5 : ℝ) / 17 < 4317 / 14677 ∧
      (3957 : ℝ) / 13453 - 4317 / 14677 = 288 / 197449681 := by
  norm_num

/-- The rational curvature branch alone gives the final integer-power exponent.
The counting inequality is an explicit hypothesis. -/
theorem polarProjection_curvature_window_power {T H X S A a C E D F K : ℕ}
    (ha : 0 < a) (hcount : T ^ 288 ≤ K * X ^ 1438 * S ^ 3)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hbox : S ^ 3 * T ^ 9 ≤ F * a ^ 3) (hdrop : T ^ 2 ≤ D * A) :
    T ^ 14677 ≤ K * (E * C ^ 6 * D ^ 2) ^ 1438 * F * a ^ 4317 := by
  simpa only [Nat.reduceMul, Nat.reduceAdd] using
    window_branch_exponent ha hcount hgap hheight hbox hdrop

/-- The exceptional curvature branch gives the exponent 717/2440. -/
theorem polarProjection_bad_curvature_window_power {T H X S A a C E D F K : ℕ}
    (ha : 0 < a) (hcount : T ^ 51 ≤ K * X ^ 238 * S ^ 3)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hbox : S ^ 3 * T ^ 9 ≤ F * a ^ 3) (hdrop : T ^ 2 ≤ D * A) :
    T ^ 2440 ≤ K * (E * C ^ 6 * D ^ 2) ^ 238 * F * a ^ 717 := by
  simpa only [Nat.reduceMul, Nat.reduceAdd] using
    window_branch_exponent ha hcount hgap hheight hbox hdrop

/-- The exceptional rank-five branch gives the exponent 732/2491. -/
theorem polarProjection_bad_rank_five_window_power {T H X Y A a C E D F K : ℕ}
    (ha : 0 < a) (hcount : T ^ 51 ≤ K * X ^ 238 * Y ^ 3)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hbox : Y ^ 3 * T ^ 60 ≤ F * a ^ 18) (hdrop : T ^ 2 ≤ D * A) :
    T ^ 2491 ≤ K * (E * C ^ 6 * D ^ 2) ^ 238 * F * a ^ 732 := by
  simpa only [Nat.reduceMul, Nat.reduceAdd] using
    window_branch_exponent ha hcount hgap hheight hbox hdrop

end
end PierceLengthBound.FixedDividend
