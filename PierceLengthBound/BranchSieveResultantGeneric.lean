/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveResultantDegree

/-! Generic irreducibility of the explicit specialization-compatible branch
resultant, using the bounded primitive-element choice. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra
local instance branchResultantGenericLocationField : Field BranchLocationField :=
  inferInstance
local instance branchResultantGenericLocationExtension : Field BranchLocationExtension :=
  inferInstance
local instance branchResultantGenericRatField : Field (RatFunc BranchLocationField) :=
  inferInstance
local instance branchResultantGenericRatExtension : Field (RatFunc BranchLocationExtension) :=
  inferInstance

lemma branchGeneric_location_sextic_eval_zero :
    (branchLocationSextic (branchGenericCoefficient 0) (branchGenericCoefficient 1)
      (branchGenericCoefficient 2)).eval (branchLocationEvaluation X) = 0 := by
  have h : branchLocationEvaluation branchGenericLocationSextic = 0 := AdjoinRoot.mk_self
  simpa [branchGenericLocationSextic, branchLocationSextic, branchGenericCoefficient,
    map_ofNat] using h

lemma branchGeneric_location_reconstruction_zero :
    (branchLocationDenominator (branchGenericCoefficient 0) (branchGenericCoefficient 1)
      (branchGenericCoefficient 2)).eval (branchLocationEvaluation X) * branchGenericThirdLocation +
    (branchLocationNumerator (branchGenericCoefficient 0) (branchGenericCoefficient 1)
      (branchGenericCoefficient 2)).eval (branchLocationEvaluation X) = 0 := by
  have hD : (branchLocationDenominator (branchGenericCoefficient 0) (branchGenericCoefficient 1)
      (branchGenericCoefficient 2)).eval (branchLocationEvaluation X) =
      branchLocationEvaluation branchGenericDenominator := by
    simp [branchGenericCoefficient, branchGenericDenominator, branchLocationDenominator,
      map_ofNat]
  have hN : (branchLocationNumerator (branchGenericCoefficient 0) (branchGenericCoefficient 1)
      (branchGenericCoefficient 2)).eval (branchLocationEvaluation X) =
      branchLocationEvaluation branchGenericNumerator := by
    simp [branchGenericCoefficient, branchGenericNumerator, branchLocationNumerator, map_ofNat]
  rw [hD, hN, branchGenericThirdLocation, mul_div_cancel₀ _ branchGenericDenominator_ne_zero]
  exact neg_add_cancel _

set_option synthInstance.maxHeartbeats 200000 in
-- The coefficient, location, scale and sign extensions form a four-stage scalar tower.
set_option maxHeartbeats 1000000 in
/-- The explicit resultant annihilates the same primitive generic label as the
norm polynomial. The proof uses the original polynomial relations. -/
theorem branchGenericResultantLabel_root (a : ℚ) (ha : a ≠ 0) (c : ℕ) :
    Polynomial.aeval (branchGenericLocationInSignAlgebra a +
      (c : BranchGenericSignAlgebra a) * branchGenericSignRoot a)
      (branchGenericResultantLabel a c) = 0 := by
  let : Fact (Irreducible (branchSignPolynomial
      (algebraMap ℚ BranchLocationExtension a) branchGenericDelta)) :=
    ⟨branchSignPolynomial_irreducible
      (by simpa only [map_zero] using (algebraMap ℚ BranchLocationExtension).injective.ne ha)
      branchGenericDelta_ne_zero⟩
  let : Field (BranchGenericSignAlgebra a) := inferInstance
  let R := RatFunc BranchLocationField
  let L := BranchLocationExtension
  let E := BranchGenericSignAlgebra a
  let φ := algebraMap R E
  let ξ := algebraMap (RatFunc L) E
  let ψ : L →+* E := ξ.comp RatFunc.C
  let t := branchLocationEvaluation X
  let y := branchGenericThirdLocation
  have hcoeff (i : Fin 3) : φ (branchResultantGenericCoefficient i) =
      ψ (branchGenericCoefficient i) := by
    change algebraMap R E (RatFunc.C (algebraMap BranchLocationParameters BranchLocationField
      (MvPolynomial.X i))) = ξ (RatFunc.C (branchGenericCoefficient i))
    rw [IsScalarTower.algebraMap_apply R (RatFunc L) E, branch_ratFunc_algebraMap_C]
    simp only [branchGenericCoefficient, branchLocationEvaluation, RingHom.coe_comp,
      Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, AdjoinRoot.mk_C]
    rfl
  have ht : ψ t = branchGenericLocationInSignAlgebra a := by
    simp only [ψ, t, branchLocationEvaluation, RingHom.coe_comp, Function.comp_apply,
      Polynomial.coe_mapRingHom, Polynomial.map_X,
      AdjoinRoot.mk_X, branchGenericLocationInSignAlgebra, ξ]
    rfl
  have hscale : φ RatFunc.X = ξ RatFunc.X := by
    rw [IsScalarTower.algebraMap_apply R (RatFunc L) E, branch_ratFunc_algebraMap_X]
  have ha' : φ (RatFunc.C (algebraMap ℚ BranchLocationField a)) =
      ψ (algebraMap ℚ L a) := by
    rw [IsScalarTower.algebraMap_apply R (RatFunc L) E, branch_ratFunc_algebraMap_C,
      ← IsScalarTower.algebraMap_apply ℚ BranchLocationField L]
    rfl
  have hΔ : ψ branchGenericDelta = branchLocationDelta 1 (ψ t) (ψ y) := by
    simp [branchGenericDelta, branchLocationDelta, t, y, map_mul]
  have hβ : φ RatFunc.X * branchGenericSignRoot a ^ 2 =
      φ (RatFunc.C (algebraMap ℚ BranchLocationField a)) *
        branchLocationDelta 1 (ψ t) (ψ y) := by
    have hh := branchSignRoot_square (algebraMap ℚ L a) branchGenericDelta
    change branchGenericSignRoot a ^ 2 = ξ (branchSignSquare (algebraMap ℚ L a)
      branchGenericDelta) at hh
    rw [hh, branchSignSquare, map_div₀, map_mul, map_mul, hscale]
    rw [mul_div_cancel₀ _ (by
      simpa only [map_zero] using ξ.injective.ne (RatFunc.X_ne_zero (K := L)))]
    rw [ha', ← hΔ]
    rfl
  have hE : (branchLocationSextic (ψ (branchGenericCoefficient 0))
      (ψ (branchGenericCoefficient 1)) (ψ (branchGenericCoefficient 2))).eval (ψ t) = 0 := by
    rw [← branchLocationSextic_map, Polynomial.eval_map_apply,
      branchGeneric_location_sextic_eval_zero, map_zero]
  have hy : (branchLocationDenominator (ψ (branchGenericCoefficient 0))
      (ψ (branchGenericCoefficient 1)) (ψ (branchGenericCoefficient 2))).eval (ψ t) * ψ y +
      (branchLocationNumerator (ψ (branchGenericCoefficient 0))
      (ψ (branchGenericCoefficient 1)) (ψ (branchGenericCoefficient 2))).eval (ψ t) = 0 := by
    rw [← branchLocationDenominator_map, ← branchLocationNumerator_map,
      Polynomial.eval_map_apply, Polynomial.eval_map_apply, ← map_mul, ← map_add,
      branchGeneric_location_reconstruction_zero, map_zero]
  have hh := branchResultantLabel_root (φ (RatFunc.C (algebraMap ℚ BranchLocationField a)))
    (φ RatFunc.X) (c : E) (ψ (branchGenericCoefficient 0)) (ψ (branchGenericCoefficient 1))
    (ψ (branchGenericCoefficient 2)) (ψ t) (ψ y) (branchGenericSignRoot a) hE hy hβ
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, branchGenericResultantLabel,
    branchResultantLabel_map]
  dsimp only [φ] at hcoeff
  rw [hcoeff 0, hcoeff 1, hcoeff 2, map_natCast]
  rw [ht] at hh
  exact hh

/-- A bounded slope makes the explicit, specialization-compatible resultant
irreducible of degree twelve for every nonzero rational dividend. -/
theorem branchGeneric_exists_irreducible_resultant_label (a : ℚ) (ha : a ≠ 0) :
    ∃ c : ℕ, c ≤ 144 ∧ Irreducible (branchGenericResultantLabel a c) ∧
      (branchGenericResultantLabel a c).natDegree = 12 := by
  let : Fact (Irreducible (branchSignPolynomial
      (algebraMap ℚ BranchLocationExtension a) branchGenericDelta)) :=
    ⟨branchSignPolynomial_irreducible
      (by simpa only [map_zero] using (algebraMap ℚ BranchLocationExtension).injective.ne ha)
      branchGenericDelta_ne_zero⟩
  obtain ⟨c, hc, hirr, hdeg⟩ := branchGeneric_exists_degree_twelve_polynomial a ha
  have hp0 : branchGenericResultantLabel a c ≠ 0 := by
    intro hz
    have hh := branchGenericResultantLabel_natDegree a c
    rw [hz, natDegree_zero] at hh
    omega
  have hdvd := minpoly.dvd (RatFunc BranchLocationField) _
    (branchGenericResultantLabel_root a ha c)
  have hassoc := Polynomial.associated_of_dvd_of_natDegree_le hdvd hp0
    (by rw [branchGenericResultantLabel_natDegree, hdeg])
  exact ⟨c, hc, hassoc.irreducible hirr, branchGenericResultantLabel_natDegree a c⟩

end
end PierceLengthBound.FixedDividend
