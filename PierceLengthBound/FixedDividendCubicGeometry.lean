/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendQuadraticGeometry
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The leading cubic is not divisible by the leading quadratic

The coefficient comparison holds over every field of characteristic zero. For the
real pattern signs `ρ > 0`, `u > 0`, `v < 0` it applies over `ℂ`.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- A polynomial of total degree at most one is affine in the three coordinates. -/
lemma eq_affine_of_totalDegree_le_one {K : Type*} [CommRing K]
    (f : MvPolynomial (Fin 3) K) (hf : f.totalDegree ≤ 1) :
    f = C (f.coeff 0) + ∑ j : Fin 3, C (f.coeff (Finsupp.single j 1)) * X j := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d
    simp [coeff_C, coeff_C_mul, coeff_X]
  by_cases hs : d.sum (fun _ e => e) = 1
  · obtain ⟨j, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp hs
    simp [coeff_C, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff, Ne.symm hd]
  have hn : 1 < d.sum (fun _ e => e) := by
    have hpos : 0 < d.sum (fun _ e => e) := by
      rw [Finsupp.sum_fintype _ (fun (_ : Fin 3) (e : ℕ) => e) (fun _ => rfl)]
      exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) (by
        obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hd
        exact ⟨j, Finset.mem_univ _, Nat.pos_of_ne_zero (by simpa using hj)⟩)
    omega
  have hz : f.coeff d = 0 := coeff_eq_zero_of_totalDegree_lt (by
    change f.totalDegree < d.sum (fun _ e => e)
    exact hf.trans_lt hn)
  have hj : ∀ j : Fin 3, Finsupp.single j 1 ≠ d := by
    intro j he
    subst d
    simp at hn
  simp [hz, coeff_C, coeff_C_mul, coeff_X, Ne.symm hd, hj]

/-- The homogeneous quadratic in the free node coordinates. -/
def leadingQuadratic {K : Type*} [CommRing K] (a b c : K) : MvPolynomial (Fin 3) K :=
  ternaryQuadratic a b c 0 0 0

/-- The homogeneous cubic in the free node coordinates. -/
def leadingCubic {K : Type*} [CommRing K] (a b c : K) : MvPolynomial (Fin 3) K :=
  C a * X 0 ^ 3 + C b * X 1 ^ 3 + C c * X 2 ^ 3 -
    (C a * X 0 + C b * X 1 + C c * X 2) ^ 3

lemma leadingQuadratic_degree {K : Type*} [Field K] [CharZero K] (a b c : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hs : 1 + a + b + c ≠ 0) :
    (leadingQuadratic a b c).totalDegree = 2 := by
  have hle := ternaryQuadratic_degree_le a b c 0 0 0
  have hnon : ¬ (leadingQuadratic a b c).totalDegree ≤ 1 := by
    intro hd
    have hh := hessian_eq_zero_of_degree_le_one hd
    have hdet : (hessianAtZero (leadingQuadratic a b c)).det = 0 := by
      rw [hh, Matrix.det_zero]
    rw [leadingQuadratic, ternaryQuadratic_hessian_det] at hdet
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb) hc) hs) hdet
  change (leadingQuadratic a b c).totalDegree ≤ 2 at hle
  omega

lemma leadingCubic_degree_le {K : Type*} [Field K] (a b c : K) :
    (leadingCubic a b c).totalDegree ≤ 3 := by
  have ht (r : K) (j : Fin 3) :
      (C r * X j ^ 3 : MvPolynomial (Fin 3) K).totalDegree ≤ 3 := by
    calc
      _ ≤ (C r : MvPolynomial (Fin 3) K).totalDegree +
        (X j ^ 3 : MvPolynomial (Fin 3) K).totalDegree := totalDegree_mul _ _
      _ = 3 := by rw [totalDegree_C, totalDegree_X_pow]
  apply (totalDegree_sub _ _).trans
  exact max_le ((totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le (ht a 0) (ht b 1))) (ht c 2)))
    ((totalDegree_pow _ 3).trans (Nat.mul_le_mul_left 3 (linear_form_degree_le a b c)))

/-- The cubic form is not the quadratic form times an affine form. -/
lemma cubic_not_quadratic_mul_affine {K : Type*} [Field K] [CharZero K]
    (a b c : K) (hb : b ≠ 0) (hb1 : 1 + b ≠ 0) (hc : c ≠ 0)
    (hc1 : 1 + c ≠ 0) (hs : 1 + b + c ≠ 0) :
    ¬ ∃ δ α β γ : K, ∀ x y z : K,
      a * x ^ 3 + b * y ^ 3 + c * z ^ 3 - (a * x + b * y + c * z) ^ 3 =
      (a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + (a * x + b * y + c * z) ^ 2) *
        (δ + α * x + β * y + γ * z) := by
  rintro ⟨δ, α, β, γ, h⟩
  have hy := h 0 1 0
  have hmy := h 0 (-1) 0
  have hz := h 0 0 1
  have hp := h 0 1 1
  have hm := h 0 1 (-1)
  norm_num at hy hmy hz hp hm
  have hδ : δ = 0 := by
    have he : (b * (1 + b)) * δ = 0 := by linear_combination -(hy + hmy) / 2
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hb hb1)
  subst δ
  have hβ : β = 1 - b := by
    have he : b * (1 + b) * (β - (1 - b)) = 0 := by linear_combination -hy
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero hb hb1))
  have hγ : γ = 1 - c := by
    have he : c * (1 + c) * (γ - (1 - c)) = 0 := by linear_combination -hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero hc hc1))
  rw [hβ, hγ] at hp hm
  have he : b * (1 + b + c) = 0 := by linear_combination -(hp - hm) / 2
  exact (mul_ne_zero hb hs) he

/-- Over a field of characteristic zero, the leading quadratic does not divide the
leading cubic under the stated nonvanishing conditions. -/
theorem leadingQuadratic_not_dvd_cubic {K : Type*} [Field K] [CharZero K]
    (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : 1 + a + b + c ≠ 0) (hb1 : 1 + b ≠ 0) (hc1 : 1 + c ≠ 0)
    (hbc : 1 + b + c ≠ 0) : ¬ leadingQuadratic a b c ∣ leadingCubic a b c := by
  rintro ⟨g, he⟩
  have hq := leadingQuadratic_degree a b c ha hb hc habc
  have hq0 : leadingQuadratic a b c ≠ 0 := by intro hz; simp [hz] at hq
  have hg : g.totalDegree ≤ 1 := by
    by_cases hg0 : g = 0
    · simp [hg0]
    have hd := leadingCubic_degree_le a b c
    rw [he, totalDegree_mul_of_isDomain hq0 hg0, hq] at hd
    omega
  have hgform := eq_affine_of_totalDegree_le_one g hg
  apply cubic_not_quadratic_mul_affine a b c hb hb1 hc hc1 hbc
  refine ⟨g.coeff 0, g.coeff (Finsupp.single 0 1), g.coeff (Finsupp.single 1 1),
    g.coeff (Finsupp.single 2 1), ?_⟩
  intro x y z
  have hev := congrArg (eval ![x, y, z]) he
  rw [hgform] at hev
  simpa [leadingQuadratic, leadingCubic, ternaryQuadratic, Fin.sum_univ_succ, add_assoc] using hev

/-- For `ρ > 0`, `u > 0`, `v < 0`, the leading quadratic does not divide the leading
cubic over `ℂ`. -/
theorem pattern_leadingQuadratic_not_dvd_cubic {ρ u v : ℝ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) :
    ¬ leadingQuadratic (-(ρ : ℂ) - u) ((u : ℂ) - v) ((v : ℂ) - 1) ∣
      leadingCubic (-(ρ : ℂ) - u) ((u : ℂ) - v) ((v : ℂ) - 1) := by
  apply leadingQuadratic_not_dvd_cubic
  all_goals exact_mod_cast (by linarith : _ ≠ (0 : ℝ))

end
end PierceLengthBound.FixedDividend
