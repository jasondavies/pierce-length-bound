/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveResultantLabel
public import PierceLengthBound.BranchSieveNormPolynomial
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The explicit branch resultant has degree twelve: over a splitting field it
is a nonzero constant times six quadratic label equations. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial


/-- The label degree of a determinant is bounded by the sum of bounds for its
columns. This bound remains valid when the coefficient ring has zero divisors. -/
lemma branch_matrix_det_natDegree_le {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (Polynomial R)) (d : ι → ℕ)
    (hd : ∀ i j, (M i j).natDegree ≤ d j) : M.det.natDegree ≤ ∑ j, d j := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  apply (Polynomial.natDegree_smul_le _ _).trans
  exact (Polynomial.natDegree_prod_le _ _).trans
    (Finset.sum_le_sum (fun j _ => hd (σ j) j))

/-- Each coefficient in the eliminated location has degree at most two in the
label, before imposing any genericity or nonvanishing conditions. -/
lemma branchLabelEliminand_coeff_natDegree_le {R : Type*} [CommRing R]
    (a A c c1 c2 c3 : R) (j : ℕ) :
    ((branchLabelEliminand a A c c1 c2 c3).coeff j).natDegree ≤ 2 := by
  let H : R[X] := C A * (branchLocationDenominator c1 c2 c3) ^ 3
  let J : R[X] := C (c ^ 2 * a) * branchDeltaNumerator c1 c2 c3
  have he : branchLabelEliminand a A c c1 c2 c3 =
      C (X ^ 2) * H.map C - C X * (2 * X * H).map C + (X ^ 2 * H - J).map C := by
    simp only [branchLabelEliminand, H, J, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_sub, Polynomial.map_ofNat,
      Polynomial.C_pow]
    ring
  rw [he]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_map]
  compute_degree

set_option maxHeartbeats 1000000 in
-- Summing the two Sylvester column blocks elaborates the fixed 17-dimensional index type.
/-- Every specialization of the explicit branch resultant has label degree at
most twelve, including degenerate sextics and vanishing scale. -/
theorem branchResultantLabel_natDegree_le {R : Type*} [CommRing R]
    (a A c c1 c2 c3 : R) : (branchResultantLabel a A c c1 c2 c3).natDegree ≤ 12 := by
  let d : Fin (6 + 11) → ℕ := Fin.addCases (fun _ : Fin 6 => 2) (fun _ : Fin 11 => 0)
  have hd : ∀ i j, ((Polynomial.sylvester ((branchLocationSextic c1 c2 c3).map C)
      (branchLabelEliminand a A c c1 c2 c3) 6 11) i j).natDegree ≤ d j := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left, d]
      split_ifs
      · exact branchLabelEliminand_coeff_natDegree_le a A c c1 c2 c3 _
      · simp
    | right j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right, d]
      split_ifs <;> simp
  have hh := branch_matrix_det_natDegree_le _ d hd
  have hs : ∑ j, d j = 12 := by
    change (∑ j : Fin (6 + 11), Fin.addCases (fun _ : Fin 6 => 2)
      (fun _ : Fin 11 => 0) j) = 12
    rw [Fin.sum_univ_add]
    simp
  simpa only [branchResultantLabel, resultant, hs] using hh

/-- Evaluating the eliminated location leaves a quadratic in the label. -/
lemma branchLabelEliminand_eval_C {K : Type*} [CommRing K]
    (a A c c1 c2 c3 t : K) :
    (branchLabelEliminand a A c c1 c2 c3).eval (C t) =
      C (A * ((branchLocationDenominator c1 c2 c3).eval t) ^ 3) * (X - C t) ^ 2 -
        C (c ^ 2 * a * (branchDeltaNumerator c1 c2 c3).eval t) := by
  simp only [branchLabelEliminand, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
    eval_map_apply, map_mul, map_pow]

lemma branchLabelEliminand_eval_C_natDegree {K : Type*} [Field K]
    (a A c c1 c2 c3 t : K) (hA : A ≠ 0)
    (hD : (branchLocationDenominator c1 c2 c3).eval t ≠ 0) :
    ((branchLabelEliminand a A c c1 c2 c3).eval (C t)).natDegree = 2 := by
  rw [branchLabelEliminand_eval_C]
  compute_degree <;> simp [hA, hD]

/-- A split sextic with no reconstruction-denominator zero contributes exactly
two label roots per location, even when the chosen slope is zero. -/
theorem branchResultantLabel_natDegree_of_splits {K : Type*} [Field K]
    (a A c c1 c2 c3 : K) (hA : A ≠ 0)
    (hdeg : (branchLocationSextic c1 c2 c3).natDegree = 6)
    (hsplit : (branchLocationSextic c1 c2 c3).Splits)
    (hD : ∀ t ∈ (branchLocationSextic c1 c2 c3).roots,
      (branchLocationDenominator c1 c2 c3).eval t ≠ 0) :
    (branchResultantLabel a A c c1 c2 c3).natDegree = 12 := by
  let e := branchLocationSextic c1 c2 c3
  let g := branchLabelEliminand a A c c1 c2 c3
  have he : e ≠ 0 := by intro hz; simp [e, hz] at hdeg
  have hm : (e.map C).natDegree = 6 := by
    rw [natDegree_map_eq_of_injective Polynomial.C_injective]
    exact hdeg
  have hs : (e.map C).Splits := hsplit.map C
  have hr : (e.map C).roots = e.roots.map C :=
    (roots_map_of_injective_of_card_eq_natDegree Polynomial.C_injective
      hsplit.natDegree_eq_card_roots.symm).symm
  have hf := resultant_eq_prod_eval (e.map C) g 11
    (branchLabelEliminand_natDegree_le a A c c1 c2 c3) hs
  rw [hm, hr, Multiset.map_map, leadingCoeff_map_of_injective Polynomial.C_injective] at hf
  have hgdeg : ∀ t ∈ e.roots, (g.eval (C t)).natDegree = 2 := by
    intro t ht
    exact branchLabelEliminand_eval_C_natDegree a A c c1 c2 c3 t hA (hD t ht)
  have hzero : (0 : K[X]) ∉ e.roots.map (fun t => g.eval (C t)) := by
    intro hz
    obtain ⟨t, ht, heq⟩ := Multiset.mem_map.mp hz
    have := hgdeg t ht
    rw [heq, natDegree_zero] at this
    omega
  change (resultant (e.map C) g 6 11).natDegree = 12
  rw [hf]
  rw [← Polynomial.C_pow, natDegree_C_mul (pow_ne_zero 11 (leadingCoeff_ne_zero.mpr he))]
  change (e.roots.map (fun t => g.eval (C t))).prod.natDegree = 12
  rw [natDegree_multiset_prod _ hzero, Multiset.map_map]
  change (e.roots.map (fun t => (g.eval (C t)).natDegree)).sum = 12
  have hmap : e.roots.map (fun t => (g.eval (C t)).natDegree) =
      e.roots.map (fun _ => 2) := Multiset.map_congr rfl hgdeg
  rw [hmap, Multiset.map_const', Multiset.sum_replicate]
  rw [← hsplit.natDegree_eq_card_roots, hdeg]
  norm_num

/-- The degree calculation descends from an algebraic closure. Coprimality
excludes every reconstruction-denominator zero at a sextic root. -/
theorem branchResultantLabel_natDegree {K : Type*} [Field K]
    (a A c c1 c2 c3 : K) (hA : A ≠ 0)
    (hdeg : (branchLocationSextic c1 c2 c3).natDegree = 6)
    (hcop : IsCoprime (branchLocationSextic c1 c2 c3) (branchLocationDenominator c1 c2 c3)) :
    (branchResultantLabel a A c c1 c2 c3).natDegree = 12 := by
  let L := AlgebraicClosure K
  let φ := algebraMap K L
  rw [← natDegree_map_eq_of_injective φ.injective, branchResultantLabel_map]
  apply branchResultantLabel_natDegree_of_splits _ _ _ _ _ _
  · simpa only [map_zero] using φ.injective.ne hA
  · rw [← branchLocationSextic_map, natDegree_map_eq_of_injective φ.injective]
    exact hdeg
  · exact IsAlgClosed.splits _
  · intro t ht hDt
    have he0 : (branchLocationSextic (φ c1) (φ c2) (φ c3)).eval t = 0 :=
      (mem_roots (by
        rw [← branchLocationSextic_map]
        apply Polynomial.map_ne_zero
        intro hz
        rw [hz, natDegree_zero] at hdeg
        omega)).mp ht
    obtain ⟨p, q, hpq⟩ := hcop.map (Polynomial.mapRingHom φ)
    have hh := congrArg (Polynomial.eval t) hpq
    simp only [Polynomial.coe_mapRingHom, branchLocationSextic_map,
      branchLocationDenominator_map, eval_add, eval_mul, he0, hDt, mul_zero, add_zero,
      eval_one] at hh
    exact zero_ne_one hh

open scoped RatFunc
attribute [local instance] Polynomial.algebra
local instance branchResultantDegreeLocationField : Field BranchLocationField := inferInstance
local instance branchResultantDegreeLocationExtension : Field BranchLocationExtension :=
  inferInstance
local instance branchResultantDegreeRatField : Field (RatFunc BranchLocationField) :=
  inferInstance
local instance branchResultantDegreeRatExtension : Field (RatFunc BranchLocationExtension) :=
  inferInstance

/-- The normalized vertex parameters in the generic scale function field. -/
def branchResultantGenericCoefficient (i : Fin 3) : RatFunc BranchLocationField :=
  RatFunc.C (algebraMap BranchLocationParameters BranchLocationField (MvPolynomial.X i))

/-- The explicit label equation in the generic vertex function field. -/
def branchGenericResultantLabel (a : ℚ) (c : ℕ) : Polynomial (RatFunc BranchLocationField) :=
  branchResultantLabel (RatFunc.C (algebraMap ℚ BranchLocationField a)) RatFunc.X c
    (branchResultantGenericCoefficient 0) (branchResultantGenericCoefficient 1)
    (branchResultantGenericCoefficient 2)

lemma branchGeneric_sextic_denominator_coprime :
    IsCoprime (branchGenericLocationSextic.map
      (algebraMap BranchLocationParameters BranchLocationField))
      (branchGenericDenominator.map (algebraMap BranchLocationParameters BranchLocationField)) := by
  apply branchGenericLocationSextic_irreducible.coprime_iff_not_dvd.mpr
  intro hd
  apply branchGenericDenominator_ne_zero
  exact AdjoinRoot.mk_eq_zero.mpr hd

/-- The explicit generic resultant is nonzero of degree twelve for every
slope and dividend; these parameters do not affect its leading coefficient. -/
theorem branchGenericResultantLabel_natDegree (a : ℚ) (c : ℕ) :
    (branchGenericResultantLabel a c).natDegree = 12 := by
  have he : (branchGenericLocationSextic.map
      (algebraMap BranchLocationParameters BranchLocationField)).map RatFunc.C =
      branchLocationSextic (branchResultantGenericCoefficient 0)
        (branchResultantGenericCoefficient 1) (branchResultantGenericCoefficient 2) := by
    rw [branchGenericLocationSextic, branchLocationSextic_map, branchLocationSextic_map]
    rfl
  have hD : (branchGenericDenominator.map
      (algebraMap BranchLocationParameters BranchLocationField)).map RatFunc.C =
      branchLocationDenominator (branchResultantGenericCoefficient 0)
        (branchResultantGenericCoefficient 1) (branchResultantGenericCoefficient 2) := by
    rw [branchGenericDenominator, branchLocationDenominator_map, branchLocationDenominator_map]
    rfl
  apply branchResultantLabel_natDegree _ _ _ _ _ _ RatFunc.X_ne_zero
  · rw [← he, natDegree_map_eq_of_injective RatFunc.C_injective,
      branchGenericLocationSextic_fraction_natDegree]
  · have hh := branchGeneric_sextic_denominator_coprime.map (Polynomial.mapRingHom RatFunc.C)
    simpa only [Polynomial.coe_mapRingHom, he, hD] using hh

end
end PierceLengthBound.FixedDividend
