/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendConicBoundedModel
public import PierceLengthBound.ConicPlaneHeight

/-! The bounded integer parabolic model at an actual Pierce orbit point. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Actual minor heights give the complete bounded integral conic model.
The only plane input is its integer coefficient bound and actual membership. -/
theorem orbit_bounded_integer_conic_model {a b i : ℕ} (hba : b < a)
    (hi : i + 7 < P a b) {X L : ℤ} (hX : 1 ≤ X) (hL : 0 ≤ L)
    (ht : ∀ j, |theta a b i j| ≤ X)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (n : Fin 3 → ℤ) (e : ℤ) (hn : n ≠ 0) (hnb : ∀ j, |n j| ≤ L) (heb : |e| ≤ L)
    (hplane : integerPlanePolynomial n e ∈ I)
    {N : ℕ} {c : ℤ}
    (hdegree : ∀ m ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = 2 * m + c)
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I) :
    ∃ (j k : Fin 3) (v : Fin 6 → ℤ), Function.Bijective ![j, 0, k] ∧ n k ≠ 0 ∧
      (∀ q, |v q| ≤ 10 * (12 * X ^ 4) ^ 2 * L ^ 2) ∧
      v 0 ≠ 0 ∧ (v 1) ^ 2 - 4 * v 0 * v 2 = 0 ∧
      2 * v 1 * v 3 - 4 * v 0 * v 4 ≠ 0 ∧
      ∀ z : Fin 3 → ℤ, (fun q => (z q : ℚ)) ∈ coordinateZeroLocus I →
        conicValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (z j) (z 0) = 0 := by
  let w := conicPatternCommon (theta a b i)
  have hw : ∀ j, |w j| ≤ X ^ 2 := conicPatternCommon_height ht
  have hratio := conicPatternCommon_orbit hba (by omega : i + 6 < P a b)
  have h0 : (w 0 : ℚ) / w 6 = patternRhoQ a b i := congrFun hratio 0
  have h1 : (w 1 : ℚ) / w 6 = patternUQ a b i := congrFun hratio 1
  have h2 : (w 2 : ℚ) / w 6 = patternVQ a b i := congrFun hratio 2
  have h3 : (w 3 : ℚ) / w 6 = patternRhoQ a b (i + 1) := congrFun hratio 3
  have h4 : (w 4 : ℚ) / w 6 = patternUQ a b (i + 1) := congrFun hratio 4
  have h5 : (w 5 : ℚ) / w 6 = patternVQ a b (i + 1) := congrFun hratio 5
  have hL0 : Lz a b i ≠ 0 := ne_of_gt (Lz_pos hba (by omega))
  have hL1 : Lz a b (i + 1) ≠ 0 := ne_of_gt (Lz_pos hba (by omega))
  have hD : w 6 ≠ 0 := mul_ne_zero hL0 hL1
  have hsign := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  have hnormal : n 0 ≠ 0 ∨ n 1 ≠ 0 ∨ n 2 ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hn
    ext j
    fin_cases j <;> simp only [Pi.zero_apply] <;> tauto
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hA : (Lz a b i : ℚ) ≠ 0 := by exact_mod_cast hL0
  have hpEq : integerPlanePolynomial n e = C (n 0 : ℚ) * MvPolynomial.X 0 +
      C (n 1 : ℚ) * MvPolynomial.X 1 + C (n 2 : ℚ) * MvPolynomial.X 2 + C (e : ℚ) := by
    simp only [integerPlanePolynomial, Fin.sum_univ_succ,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring
  rw [hpEq] at hplane
  have hh := nonexceptional_bounded_integer_conic_model
    (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (n 0) (n 1) (n 2) e
    (M := X ^ 2) (by nlinarith) hL hD (hw 0) (hw 1) (hw 2) (hw 3) (hw 4) (hw 5) (hw 6)
    (hnb 0) (hnb 1) (hnb 2) heb
    (by simpa only [h0] using hsign.1) (by simpa only [h1] using hsign.2.1)
    (by simpa only [h2] using hsign.2.2)
    (by simpa only [h0, h1, h2, patternRhoQ_cast, patternUQ_cast, patternVQ_cast] using hne)
    (Lz a b i) a hA ha I
    (by simpa only [h0, h1, h2, h3, h4, h5, orbitCurveQuadraticQ] using hf)
    (by simpa only [h0, h1, h2, h3, h4, h5, orbitCurveEquationQ] using hg)
    hnormal hplane hdegree (orbitFreeNodesQ a b i) hx
  have he : (![n 0, n 1, n 2] : Fin 3 → ℤ) = n := by ext j; fin_cases j <;> rfl
  simpa only [he, ← pow_mul, Nat.reduceMul] using hh

end
end PierceLengthBound.FixedDividend
