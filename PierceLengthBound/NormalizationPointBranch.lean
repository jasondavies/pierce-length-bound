/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.NormalizationBranchCover
public import Mathlib.RingTheory.Ideal.GoingUp

/-! A nonzero function vanishing at an affine point has a zero on a branch of
the normalization. Functions nonzero at that point have order zero there. The zero is also
realized on the normalization of a model finite over `1/t`, for `t` nonzero at the point,
outside its fiber over infinity (the last step of the proof of Lemma 8.10). Functions with a
zero or a pole at an order nonnegative on the constants are transcendental. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- A function with a pole at an order nonnegative on `K` is transcendental over `K`. -/
theorem transcendental_of_negative_order {K L : Type*} [Field K] [Field L] [Algebra K L]
    (ν : AddValuation L (WithTop ℤ)) (hK : ∀ c : K, 0 ≤ ν (algebraMap K L c))
    {x : L} (hneg : ν x < 0) : Transcendental K x := by
  intro halg
  exact (not_lt_of_ge (branch_order_nonnegative_of_integral ν hK halg.isIntegral)) hneg

/-- A nonzero function with a zero at an order nonnegative on `K` is transcendental over
`K`. -/
theorem transcendental_of_positive_order {K L : Type*} [Field K] [Field L] [Algebra K L]
    (ν : AddValuation L (WithTop ℤ)) (hK : ∀ c : K, 0 ≤ ν (algebraMap K L c))
    {x : L} (hx : x ≠ 0) (hpos : 0 < ν x) : Transcendental K x := by
  intro halg
  have hh := branch_order_nonnegative_of_integral ν hK halg.inv.isIntegral
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ν.ne_top_iff.mpr hx)
  rw [ν.map_inv, ← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg] at hh
  rw [← hn] at hpos
  have hnpos : 0 < n := by exact_mod_cast hpos
  have hnneg : 0 ≤ -n := by exact_mod_cast hh
  omega

/-- Given a ring map `φ : R → K` to a field whose kernel contains a nonzero `r`, some branch
of the normalization of `R` lies above `ker φ`: the elements of `R` with positive order there
are exactly those with `φ s = 0`. -/
theorem normalization_branch_above_point {R K L : Type*}
    [CommRing R] [IsDomain R] [Field K] [Field L] [Algebra R L] [IsFractionRing R L]
    [IsDedekindDomain (integralClosure R L)]
    (φ : R →+* K) {r : R} (hr : r ≠ 0) (hrφ : φ r = 0) :
    let C := integralClosure R L
    let : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension R L L C
    ∃ p : IsDedekindDomain.HeightOneSpectrum C,
      ∀ s : R, 0 < normalizedBranchOrder p L (algebraMap R L s) ↔ φ s = 0 := by
  let C := integralClosure R L
  let : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension R L L C
  have hinj : Function.Injective (algebraMap R C) := by
    intro a b hab
    apply IsFractionRing.injective R L
    exact congrArg (fun z : C => (z : L)) hab
  let : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, hQprime, hQ⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := C) (RingHom.ker φ)
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have hmem (s : R) : algebraMap R C s ∈ Q ↔ φ s = 0 := by
    change s ∈ Q.under R ↔ _
    rw [hQ]
    rfl
  have hQ0 : Q ≠ ⊥ := by
    intro he
    have hh := (hmem r).mpr hrφ
    rw [he, Ideal.mem_bot] at hh
    exact hr (hinj (by simpa using hh))
  let p : IsDedekindDomain.HeightOneSpectrum C := ⟨Q, hQprime, hQ0⟩
  refine ⟨p, fun s => ?_⟩
  rw [IsScalarTower.algebraMap_apply R C L,
    normalizedBranchOrder_positive_iff]
  exact hmem s

/-- If `φ r = 0` with `r ≠ 0` and `φ s ≠ 0`, then `r / s` has a zero at a branch above `ker φ`
at which every `t` with `φ t ≠ 0` has order zero. -/
theorem normalization_branch_rational_zero {R K L : Type*}
    [CommRing R] [IsDomain R] [Field K] [Field L] [Algebra R L] [IsFractionRing R L]
    [IsDedekindDomain (integralClosure R L)]
    (φ : R →+* K) {r s : R} (hr : r ≠ 0) (hrφ : φ r = 0) (hsφ : φ s ≠ 0) :
    let C := integralClosure R L
    let : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension R L L C
    ∃ p : IsDedekindDomain.HeightOneSpectrum C,
      0 < normalizedBranchOrder p L (algebraMap R L r / algebraMap R L s) ∧
      ∀ t : R, φ t ≠ 0 → normalizedBranchOrder p L (algebraMap R L t) = 0 := by
  let C := integralClosure R L
  let : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension R L L C
  obtain ⟨p, hp⟩ := normalization_branch_above_point (L := L) φ hr hrφ
  have hzero (t : R) (ht : φ t ≠ 0) :
      normalizedBranchOrder p L (algebraMap R L t) = 0 := by
    apply le_antisymm
    · exact le_of_not_gt (fun h => ht ((hp t).mp h))
    · rw [IsScalarTower.algebraMap_apply R C L]
      exact normalizedBranchOrder_nonnegative p L _
  refine ⟨p, ?_, hzero⟩
  rw [(normalizedBranchOrder p L).map_div, hzero s hsφ, sub_zero]
  exact (hp r).mpr hrφ

/-- At a rational point `φ` with `φ r = 0`, `φ s ≠ 0` and `φ t ≠ 0`, the zero of `r / s` is
realized on the normalization of a model `S` finite over `ℚ[w]`, `w = 1/t`, at a branch not in
the zero fiber of `w` (the fiber over infinity). -/
theorem rational_zero_on_reciprocal_parameter_model {R S L : Type*}
    [CommRing R] [IsDomain R] [Algebra ℚ R]
    [CommRing S] [IsDomain S] [Algebra ℚ S]
    [Field L] [Algebra ℚ L] [Algebra R L] [IsScalarTower ℚ R L] [IsFractionRing R L]
    [Algebra S L] [IsScalarTower ℚ S L] [IsFractionRing S L]
    [IsDedekindDomain (integralClosure R L)]
    [IsDedekindDomain (integralClosure S L)]
    (φ : R →ₐ[ℚ] ℚ) {r s t : R}
    (hr : r ≠ 0) (hrφ : φ r = 0) (hsφ : φ s ≠ 0) (htφ : φ t ≠ 0)
    (w : S) [Module.Finite (Algebra.adjoin ℚ {w}) S]
    (hw : algebraMap S L w = (algebraMap R L t)⁻¹) :
    let C := integralClosure S L
    let : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension S L L C
    ∃ q : IsDedekindDomain.HeightOneSpectrum C,
      0 < normalizedBranchOrder q L (algebraMap R L r / algebraMap R L s) ∧
      algebraMap S C w ∉ q.asIdeal := by
  let A := integralClosure R L
  let C := integralClosure S L
  let : IsFractionRing A L := IsIntegralClosure.isFractionRing_of_finite_extension R L L A
  let : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension S L L C
  obtain ⟨p, hpos, hunit⟩ := normalization_branch_rational_zero
    (L := L) φ.toRingHom hr hrφ hsφ
  let ν := normalizedBranchOrder p L
  have hQ (c : ℚ) : 0 ≤ ν (algebraMap ℚ L c) := by
    rw [IsScalarTower.algebraMap_apply ℚ R L, IsScalarTower.algebraMap_apply R A L]
    exact normalizedBranchOrder_nonnegative p L _
  have hw0 : ν (algebraMap S L w) = 0 := by
    rw [hw, ν.map_inv, hunit t htφ, neg_zero]
  have hS := branch_order_nonnegative_of_finite_parameter w ν hQ (le_of_eq hw0.symm)
  obtain ⟨q, hq⟩ := regular_branch_realized ν
    (branch_order_nonnegative_on_normalization ν hS) (normalizedBranchOrder_uniformizer p L)
  refine ⟨q, ?_, ?_⟩
  · rw [hq]
    exact hpos
  · intro hmem
    have hh := (normalizedBranchOrder_positive_iff q L (algebraMap S C w)).mpr hmem
    rw [hq, ← IsScalarTower.algebraMap_apply S C L, hw0] at hh
    exact lt_irrefl 0 hh

end
end PierceLengthBound.FixedDividend
