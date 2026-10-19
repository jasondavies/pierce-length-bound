/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendMoments
public import PierceLengthBound.FixedDividendResultant
public import PierceLengthBound.FixedDividendExponent
public import PierceLengthBound.ElevenCount
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Algebra for the fixed-dividend refinement

These lemmas verify parts of the `13/44` proof candidate. They do not yet establish its
local curve count or the bound for `P`. In particular, the external uniform curve-counting
input is not an axiom of this module.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

/-- Newton coefficients of the normalized monic quartic. -/
def coeffs (ρ u v : ℝ) : Fin 5 → ℝ := ![ρ, -ρ - u, u - v, v - 1, 1]

lemma coeffs_sum (ρ u v : ℝ) : ∑ j, coeffs ρ u v j = 0 := by
  simp [coeffs, Fin.sum_univ_succ]

/-- The signs used when classifying possible two-element clusters. -/
lemma coeffs_signs {ρ u v : ℝ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) :
    0 < coeffs ρ u v 0 ∧ coeffs ρ u v 1 < 0 ∧ 0 < coeffs ρ u v 2 ∧
      coeffs ρ u v 3 < -1 ∧ coeffs ρ u v 4 = 1 := by
  simp only [coeffs, Matrix.cons_val]
  constructor
  · exact hρ
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · trivial

/-- Every vanishing pair gives one of the four exceptional pattern relations. -/
theorem pair_exceptional {ρ u v : ℝ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    {j l : Fin 5} (hjl : j < l) (h : coeffs ρ u v j + coeffs ρ u v l = 0) :
    ρ + v - 1 = 0 ∨ ρ + v = 0 ∨ u - 1 = 0 ∨ 1 - ρ - u = 0 := by
  fin_cases j <;> fin_cases l <;> norm_num at hjl
  all_goals norm_num [coeffs] at h
  all_goals first
    | (exfalso; linarith)
    | (left; linarith)
    | (right; left; linarith)
    | (right; right; left; linarith)
    | (right; right; right; linarith)

/-- The leading quadratic after eliminating the fourth node. -/
def quadratic (a b c x y z : ℝ) : ℝ :=
  a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + (a * x + b * y + c * z) ^ 2

/-- The leading cubic after eliminating the fourth node. -/
def cubic (a b c x y z : ℝ) : ℝ :=
  a * x ^ 3 + b * y ^ 3 + c * z ^ 3 - (a * x + b * y + c * z) ^ 3

/-- Determinant of the matrix of the leading quadratic. -/
lemma quadratic_det (a b c : ℝ) :
    Matrix.det (!![a + a ^ 2, a * b, a * c;
                  a * b, b + b ^ 2, b * c;
                  a * c, b * c, c + c ^ 2]) = a * b * c * (1 + a + b + c) := by
  simp [Matrix.det_fin_three]
  ring

/-- The determinant is nonzero for the actual coefficient signs. -/
theorem quadratic_det_ne_zero {ρ u v : ℝ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) :
    (-ρ - u) * (u - v) * (v - 1) * (1 + (-ρ - u) + (u - v) + (v - 1)) ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (by linarith) (by linarith)
    · linarith
  · linarith

/-- The cubic is not the quadratic times a linear form. This verifies the coefficient
obstruction in the candidate without a numerical specialization of the coefficients. -/
theorem cubic_not_quadratic_mul_linear {a b c : ℝ} (hb : 0 < b) (hc : c < -1)
    (hs : 0 < 1 + b + c) :
    ¬ ∃ α β γ : ℝ, ∀ x y z : ℝ,
      cubic a b c x y z = quadratic a b c x y z * (α * x + β * y + γ * z) := by
  rintro ⟨α, β, γ, h⟩
  have hy := h 0 1 0
  have hz := h 0 0 1
  have hp := h 0 1 1
  have hm := h 0 1 (-1)
  simp only [cubic, quadratic] at hy hz hp hm
  norm_num at hy hz hp hm
  have hβ : β = 1 - b := by
    have he : b * (1 + b) * (β - (1 - b)) = 0 := by linear_combination -hy
    have hn : b * (1 + b) ≠ 0 := mul_ne_zero (ne_of_gt hb) (by linarith)
    have := (mul_eq_zero.mp he).resolve_left hn
    linarith
  have hγ : γ = 1 - c := by
    have he : c * (1 + c) * (γ - (1 - c)) = 0 := by linear_combination -hz
    have hn : c * (1 + c) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
    have := (mul_eq_zero.mp he).resolve_left hn
    linarith
  rw [hβ, hγ] at hp hm
  have he : b * (1 + b + c) = 0 := by
    linear_combination -(hp - hm) / 2
  exact (ne_of_gt (mul_pos hb hs)) he

/-- The candidate's coefficients satisfy the cubic obstruction. -/
theorem pattern_cubic_obstruction {ρ u v : ℝ} (hu : 0 < u) (hv : v < 0) :
    ¬ ∃ α β γ : ℝ, ∀ x y z : ℝ,
      cubic (-ρ - u) (u - v) (v - 1) x y z =
        quadratic (-ρ - u) (u - v) (v - 1) x y z * (α * x + β * y + γ * z) :=
  cubic_not_quadratic_mul_linear (by linarith) (by linarith) (by linarith)

/-- Four vanishing moments annihilate every cluster weight when at most four distinct
nodes remain. This is the Vandermonde step, including repeated nodes. -/
theorem cluster_sums_zero (c z : Fin 5 → ℝ)
    (hcard : (Finset.univ.image z).card ≤ 4)
    (hmom : ∀ m < 4, ∑ j : Fin 5, c j * z j ^ m = 0) :
    ∀ i, ∑ j ∈ Finset.univ.filter (fun j => z j = z i), c j = 0 := by
  classical
  let S := Finset.univ.image z
  let w (x : ℝ) := ∑ j ∈ Finset.univ.filter (fun j => z j = x), c j
  let e := (Fintype.equivFin S).symm
  have hgroup : ∀ m < 4, ∑ x : S, w x * (x : ℝ) ^ m = 0 := by
    intro m hm
    calc (∑ x : S, w x * (x : ℝ) ^ m) = ∑ x ∈ S, w x * x ^ m :=
          Finset.sum_coe_sort S (fun x => w x * x ^ m)
      _ =
        ∑ x ∈ S, ∑ j ∈ Finset.univ.filter (fun j => z j = x), c j * z j ^ m := by
          refine Finset.sum_congr rfl fun x hx => ?_
          dsimp only [w]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [(Finset.mem_filter.mp hj).2]
      _ = ∑ j : Fin 5, c j * z j ^ m :=
        Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem z hj) _
      _ = 0 := hmom m hm
  have hinj : Function.Injective (fun j : Fin (Fintype.card S) => (e j : ℝ)) := by
    intro j l h
    exact e.injective (Subtype.ext h)
  have hw : (fun j : Fin (Fintype.card S) => w (e j)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj
    intro m
    have hm : (m : ℕ) < 4 := by
      have hn : Fintype.card S ≤ 4 := by simpa only [Fintype.card_coe] using hcard
      exact m.isLt.trans_le hn
    calc (∑ j : Fin (Fintype.card S), w (e j) * (e j : ℝ) ^ (m : ℕ)) =
        ∑ x : S, w x * (x : ℝ) ^ (m : ℕ) := Equiv.sum_comp e (fun x : S => w x * (x : ℝ) ^ (m : ℕ))
      _ = 0 := hgroup m hm
  intro i
  let xi : S := ⟨z i, Finset.mem_image_of_mem z (Finset.mem_univ i)⟩
  have he := congrFun hw (e.symm xi)
  simpa only [e.apply_symm_apply, Pi.zero_apply] using he

/-- Five nonzero weights with zero sum on each node cluster, and at least two clusters,
force a two-element cluster. This is the finite combinatorial step in the line argument. -/
theorem five_cluster_pair (c z : Fin 5 → ℝ) (hc : ∀ j, c j ≠ 0)
    (hz : ∃ i j, z i ≠ z j)
    (hs : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => z j = z i), c j = 0) :
    ∃ j l : Fin 5, j ≠ l ∧ c j + c l = 0 := by
  classical
  let F (i : Fin 5) := Finset.univ.filter (fun j => z j = z i)
  have hmem : ∀ i, i ∈ F i := by intro i; simp [F]
  have hsize : ∀ i, 2 ≤ (F i).card := by
    intro i
    by_contra h
    have hsmall : (F i).card ≤ 1 := by omega
    have he : F i = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hmem i, fun j hj => Finset.card_le_one.mp hsmall j hj i (hmem i)⟩
    have hsum : ∑ j ∈ F i, c j = 0 := hs i
    rw [he, Finset.sum_singleton] at hsum
    exact hc i hsum
  have hpair : ∀ i, (F i).card = 2 → ∃ j l : Fin 5, j ≠ l ∧ c j + c l = 0 := by
    intro i hi
    obtain ⟨j, l, hjl, he⟩ := Finset.card_eq_two.mp hi
    refine ⟨j, l, hjl, ?_⟩
    have hsum : ∑ j ∈ F i, c j = 0 := hs i
    simpa [he, hjl] using hsum
  obtain ⟨i, j, hij⟩ := hz
  by_cases hi : (F i).card = 2
  · exact hpair i hi
  by_cases hj : (F j).card = 2
  · exact hpair j hj
  have hd : Disjoint (F i) (F j) := by
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    have hki' : z k = z i := (Finset.mem_filter.mp hki).2
    have hkj' : z k = z j := (Finset.mem_filter.mp hkj).2
    exact hij (hki'.symm.trans hkj')
  have hcard : (F i).card + (F j).card ≤ 5 := by
    rw [← Finset.card_union_of_disjoint hd]
    exact (Finset.card_le_univ _).trans (by decide)
  have := hsize i
  have := hsize j
  omega

/-- The leading equations of a nonconstant line imply an exceptional coefficient pair. -/
theorem line_direction_exceptional {ρ u v : ℝ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (z : Fin 5 → ℝ) (hz : ∃ i j, z i ≠ z j)
    (hcard : (Finset.univ.image z).card ≤ 4)
    (hmom : ∀ m < 4, ∑ j : Fin 5, coeffs ρ u v j * z j ^ m = 0) :
    ρ + v - 1 = 0 ∨ ρ + v = 0 ∨ u - 1 = 0 ∨ 1 - ρ - u = 0 := by
  have hc : ∀ j, coeffs ρ u v j ≠ 0 := by
    intro j
    fin_cases j <;> norm_num [coeffs] <;> linarith
  obtain ⟨j, l, hjl, hsum⟩ := five_cluster_pair (coeffs ρ u v) z hc hz
    (cluster_sums_zero _ _ hcard hmom)
  rcases lt_or_gt_of_ne hjl with hjl | hjl
  · exact pair_exceptional hρ hu hv hjl hsum
  · exact pair_exceptional hρ hu hv hjl (by linarith)

/-- Each exceptional relation is a minor after a bounded integral column change.
The displayed transformations use only column additions and permutations. -/
theorem exceptional_minors (M : Fin 3 → Fin 5 → ℤ) :
    minor3 (fun r => ![M r 1, M r 2 + M r 0, M r 3 - M r 0, M r 0, M r 4]) 0 1 2 =
      minor3 M 1 2 3 - minor3 M 0 1 3 - minor3 M 0 1 2 ∧
    minor3 (fun r => ![M r 1, M r 2 + M r 0, M r 3, M r 0, M r 4]) 0 1 2 =
      minor3 M 1 2 3 - minor3 M 0 1 3 ∧
    minor3 (fun r => ![M r 0, M r 2, M r 3 + M r 1, M r 1, M r 4]) 0 1 2 =
      minor3 M 0 2 3 - minor3 M 0 1 2 ∧
    minor3 (fun r => ![M r 0 + M r 1, M r 2, M r 3 + M r 1, M r 1, M r 4]) 0 1 2 =
      minor3 M 1 2 3 + minor3 M 0 2 3 - minor3 M 0 1 2 := by
  norm_num [minor3]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The saving and the ordering of the two exponent contributions. -/
lemma exponent_comparison :
    (45 : ℚ) / 152 - 13 / 44 = 1 / 1672 ∧ (31 : ℚ) / 105 < 13 / 44 := by
  norm_num

end PierceLengthBound.FixedDividend
