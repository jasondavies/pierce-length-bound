/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftCoordinateSystem
public import Mathlib.RingTheory.Localization.Away.Basic

/-! The actual prime ideal of a rational graph, constructed in the localization
at its denominator. This construction does not assert a graph degree bound. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

abbrev graphLocalization {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K) :=
  Localization.Away (Ideal.Quotient.mk I Q)

/-- Evaluate the new coordinate at P/Q and the old coordinates at their images. -/
def rationalGraphMap {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (P Q : MvPolynomial σ K) :
    MvPolynomial (Option σ) K →ₐ[K] graphLocalization I Q :=
  MvPolynomial.aeval (fun j => match j with
    | none => algebraMap (MvPolynomial σ K ⧸ I) (graphLocalization I Q)
        (Ideal.Quotient.mk I P) * IsLocalization.Away.invSelf (Ideal.Quotient.mk I Q)
    | some i => algebraMap (MvPolynomial σ K ⧸ I) (graphLocalization I Q)
        (Ideal.Quotient.mk I (MvPolynomial.X i)))

/-- The ideal defining the closure of the graph on the denominator-open set. -/
def rationalGraphIdeal {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (P Q : MvPolynomial σ K) :
    Ideal (MvPolynomial (Option σ) K) := RingHom.ker (rationalGraphMap I P Q)

/-- The graph ideal is prime whenever the base ideal is prime and the
rational function's denominator does not vanish identically. -/
theorem rationalGraphIdeal_isPrime {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (P Q : MvPolynomial σ K)
    (hQ : Q ∉ I) : (rationalGraphIdeal I P Q).IsPrime := by
  have hQ0 : Ideal.Quotient.mk I Q ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hQ
  let : IsDomain (graphLocalization I Q) := Localization.Away.isDomain hQ0
  exact RingHom.ker_isPrime (rationalGraphMap I P Q)

/-- Evaluation on the base curve extends to the denominator-open localization. -/
def graphPointMap {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (z : σ → K) (hz : z ∈ coordinateZeroLocus I) (hQ : MvPolynomial.eval z Q ≠ 0) :
    graphLocalization I Q →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (Ideal.Quotient.mk I Q)
    (f := Ideal.Quotient.liftₐ I (MvPolynomial.aeval z)
      (by intro f hf; exact hz f hf))
    (by
      change IsUnit (MvPolynomial.eval z Q)
      exact isUnit_iff_ne_zero.mpr hQ)

lemma graphPointMap_mk {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (z : σ → K) (hz : z ∈ coordinateZeroLocus I) (hQ : MvPolynomial.eval z Q ≠ 0)
    (f : MvPolynomial σ K) :
    graphPointMap I Q z hz hQ
      (algebraMap (MvPolynomial σ K ⧸ I) (graphLocalization I Q) (Ideal.Quotient.mk I f)) =
      MvPolynomial.eval z f := by
  simp [graphPointMap, IsLocalization.Away.liftAlgHom_apply, Ideal.Quotient.liftₐ_apply]

lemma graphPointMap_invSelf {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (Q : MvPolynomial σ K)
    (z : σ → K) (hz : z ∈ coordinateZeroLocus I) (hQ : MvPolynomial.eval z Q ≠ 0) :
    graphPointMap I Q z hz hQ (IsLocalization.Away.invSelf (Ideal.Quotient.mk I Q)) =
      (MvPolynomial.eval z Q)⁻¹ := by
  have h := congrArg (graphPointMap I Q z hz hQ)
    (IsLocalization.Away.mul_invSelf (S := graphLocalization I Q) (Ideal.Quotient.mk I Q))
  rw [map_mul, map_one, graphPointMap_mk] at h
  exact eq_inv_of_mul_eq_one_right h

/-- Every base point where Q is nonzero lifts to an actual point of the graph. -/
theorem rationalGraph_point {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (P Q : MvPolynomial σ K)
    (z : σ → K) (hz : z ∈ coordinateZeroLocus I) (hQ : MvPolynomial.eval z Q ≠ 0) :
    (fun j => match j with
      | none => MvPolynomial.eval z P / MvPolynomial.eval z Q
      | some i => z i) ∈ coordinateZeroLocus (rationalGraphIdeal I P Q) := by
  let w : Option σ → K := fun j => match j with
    | none => MvPolynomial.eval z P / MvPolynomial.eval z Q
    | some i => z i
  have hc : (graphPointMap I Q z hz hQ).comp (rationalGraphMap I P Q) =
      MvPolynomial.aeval w := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | none => simp [rationalGraphMap, w, graphPointMap_mk, graphPointMap_invSelf, div_eq_mul_inv]
    | some i => simp [rationalGraphMap, w, graphPointMap_mk]
  intro f hf
  have hf0 : rationalGraphMap I P Q f = 0 := hf
  have he := congrArg (fun h : MvPolynomial (Option σ) K →ₐ[K] K => h f) hc
  rw [AlgHom.comp_apply, hf0, map_zero] at he
  exact he.symm


set_option synthInstance.maxHeartbeats 200000 in
-- Nested quotient/localization algebras require additional instance-search time.
lemma rationalGraphMap_rename {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (P Q f : MvPolynomial σ K) :
    rationalGraphMap I P Q (MvPolynomial.rename some f) =
      algebraMap (MvPolynomial σ K ⧸ I) (graphLocalization I Q) (Ideal.Quotient.mk I f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [rename_C]
    have h1 : rationalGraphMap I P Q (C c) = algebraMap K (graphLocalization I Q) c :=
      (rationalGraphMap I P Q).commutes c
    rw [h1]
    exact IsScalarTower.algebraMap_apply K (MvPolynomial σ K ⧸ I) (graphLocalization I Q) c
  | add f g hf hg =>
    rw [map_add, map_add, hf, hg, map_add, map_add]
  | mul_X f j hf =>
    rw [map_mul, map_mul, hf, map_mul, map_mul, rename_X]
    congr 1
    simp [rationalGraphMap]

/-- The explicit graph equation belongs to its defining ideal. -/
theorem rationalGraph_equation_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (P Q : MvPolynomial σ K) :
    MvPolynomial.rename some Q * MvPolynomial.X none - MvPolynomial.rename some P ∈
      rationalGraphIdeal I P Q := by
  change rationalGraphMap I P Q _ = 0
  rw [map_sub, map_mul, rationalGraphMap_rename, rationalGraphMap_rename]
  have hX : rationalGraphMap I P Q (X none) =
      algebraMap (MvPolynomial σ K ⧸ I) (graphLocalization I Q) (Ideal.Quotient.mk I P) *
        IsLocalization.Away.invSelf (S := graphLocalization I Q) (Ideal.Quotient.mk I Q) := by
    simp [rationalGraphMap]
  rw [hX]
  rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one, sub_self]

/-- The old-coordinate contraction is exactly the base ideal. -/
theorem rationalGraph_rename_mem_iff {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (P Q f : MvPolynomial σ K)
    (hQ : Q ∉ I) :
    MvPolynomial.rename some f ∈ rationalGraphIdeal I P Q ↔ f ∈ I := by
  have hQ0 : Ideal.Quotient.mk I Q ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hQ
  have hinj : Function.Injective
      (algebraMap (MvPolynomial σ K ⧸ I) (graphLocalization I Q)) := by
    apply IsLocalization.injective (M := Submonoid.powers (Ideal.Quotient.mk I Q))
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hQ0)
  change rationalGraphMap I P Q (MvPolynomial.rename some f) = 0 ↔ _
  rw [rationalGraphMap_rename, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]

/-- The concrete ideal for the orbit's rank-three Hankel lift. -/
def orbitLiftGraphIdeal (a b i : ℕ) (I : Ideal (MvPolynomial (Fin 3) ℚ)) :
    Ideal (MvPolynomial (Option (Fin 3)) ℚ) :=
  rationalGraphIdeal I (orbitLiftNumeratorQ a b i) (orbitLiftDenominatorQ a b i)

theorem orbitLiftGraphIdeal_isPrime {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I) :
    (orbitLiftGraphIdeal a b i I).IsPrime :=
  rationalGraphIdeal_isPrime I _ _ (orbitLift_denominator_not_mem hba hi I hx)

set_option maxHeartbeats 2000000 in
-- Comparing the expanded cofactor expressions is expensive.
/-- The fourth coordinate of the actual graph point is the positive integer I3. -/
theorem orbitLiftGraph_point {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I) :
    (fun j => match j with
      | none => (integralLiftCoordinate a b i : ℚ)
      | some k => orbitFreeNodesQ a b i k) ∈ coordinateZeroLocus (orbitLiftGraphIdeal a b i I) := by
  have hp := rationalGraph_point I (orbitLiftNumeratorQ a b i)
    (orbitLiftDenominatorQ a b i) (orbitFreeNodesQ a b i) hx (orbitLift_evaluation hba hi).1
  have he : (fun j : Option (Fin 3) => match j with
      | none => (integralLiftCoordinate a b i : ℚ)
      | some k => orbitFreeNodesQ a b i k) =
      (fun j => match j with
      | none => eval (orbitFreeNodesQ a b i) (orbitLiftNumeratorQ a b i) /
          eval (orbitFreeNodesQ a b i) (orbitLiftDenominatorQ a b i)
      | some k => orbitFreeNodesQ a b i k) := by
    funext j
    cases j with
    | none => exact (orbitLift_evaluation hba hi).2
    | some k => rfl
  rw [he]
  change _ ∈ coordinateZeroLocus (rationalGraphIdeal I _ _)
  convert hp using 1
  funext j
  cases j <;> rfl

end
end PierceLengthBound.FixedDividend
