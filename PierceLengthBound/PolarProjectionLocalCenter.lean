/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionBaseSection
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import PierceLengthBound.FixedDividendRationalComponents

/-! A common zero of the polar coordinates is centered at their maximal
base ideal. Its valuation is therefore regular on the corresponding local
curve ring, supplying the center condition of the normalization comparison. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Subtracting the value at a point leaves an element of the ideal of the
centered coordinates, in every polynomially presented algebra. -/
theorem polynomial_sub_value_mem_centered_ideal {K A σ : Type*}
    [CommRing K] [CommRing A] [Algebra K A]
    (φ : MvPolynomial σ K →ₐ[K] A) (z : σ → K) (f : MvPolynomial σ K) :
    φ f - algebraMap K A (MvPolynomial.eval z f) ∈
      Ideal.span (Set.range (fun j => φ (MvPolynomial.X j) - algebraMap K A (z j))) := by
  let I := Ideal.span
    (Set.range (fun j => φ (MvPolynomial.X j) - algebraMap K A (z j)))
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg =>
    convert I.add_mem hf hg using 1
    simp only [map_add]
    ring
  | mul_X f j hf =>
    have hj : φ (MvPolynomial.X j) - algebraMap K A (z j) ∈ I :=
      Ideal.subset_span (Set.mem_range_self j)
    have h := I.add_mem (I.mul_mem_left (φ f) hj)
      (I.mul_mem_right (algebraMap K A (z j)) hf)
    convert h using 1
    simp only [map_mul, MvPolynomial.eval_X]
    ring

/-- In an affine coordinate ring, the centered coordinate ideal is exactly
the kernel of evaluation at the point. -/
theorem coordinatePoint_ker_eq_centered_ideal {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∈ coordinateZeroLocus I) :
    RingHom.ker (coordinatePoint I z hz).toRingHom =
      Ideal.span (Set.range (fun j => Ideal.Quotient.mk I (MvPolynomial.X j) -
        algebraMap K (MvPolynomial σ K ⧸ I) (z j))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hf : MvPolynomial.eval z f = 0 := by
      simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        coordinatePoint_mk] using hx
    have h := polynomial_sub_value_mem_centered_ideal (Ideal.Quotient.mkₐ K I) z f
    simpa only [hf, map_zero, sub_zero, Ideal.Quotient.mkₐ_eq_mk] using h
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change coordinatePoint I z hz _ = 0
    simp

theorem coordinatePoint_kernel_isMaximal {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∈ coordinateZeroLocus I) :
    (RingHom.ker (coordinatePoint I z hz).toRingHom).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨algebraMap K (MvPolynomial σ K ⧸ I) c, (coordinatePoint I z hz).commutes c⟩

/-- The local ring at a rational point has residue degree one. -/
theorem rational_point_local_residue_finrank {K A R : Type*} [Field K]
    [CommRing A] [Algebra K A] [CommRing R] [IsLocalRing R]
    [Algebra K R] [Algebra A R] [IsScalarTower K A R]
    (p : Ideal A) [p.IsMaximal] [IsLocalization.AtPrime R p]
    (φ : A →ₐ[K] K) (hp : RingHom.ker φ.toRingHom = p) :
    Module.finrank K (IsLocalRing.ResidueField R) = 1 := by
  have hsurj : Function.Surjective φ := fun c => ⟨algebraMap K A c, φ.commutes c⟩
  have hbase : Module.finrank K (A ⧸ p) = 1 := by
    rw [← hp]
    exact (Ideal.quotientKerAlgEquivOfSurjective hsurj).toLinearEquiv.finrank_eq.trans
      (Module.finrank_self K)
  have hloc :=
    ((IsLocalization.AtPrime.equivQuotMaximalIdeal p R).restrictScalars K).toLinearEquiv.finrank_eq
  exact hloc.symm.trans hbase

/-- A branch centered at a maximal ideal extends regularly to the local
ring there: every allowed denominator has order zero. -/
theorem branch_order_nonnegative_on_localization {A R L : Type*}
    [CommRing A] [CommRing R] [Field L] [Algebra A R] [Algebra A L]
    [Algebra R L] [IsScalarTower A R L]
    (p : Ideal A) [p.IsMaximal] [IsLocalization.AtPrime R p]
    (ν : AddValuation L (WithTop ℤ))
    (hA : ∀ a : A, 0 ≤ ν (algebraMap A L a))
    (hp : p ≤ branchCenterIdeal ν hA) :
    ∀ r : R, 0 ≤ ν (algebraMap R L r) := by
  have he : branchCenterIdeal ν hA = p :=
    (Ideal.IsMaximal.eq_of_le ‹p.IsMaximal›
      (branchCenterIdeal_isPrime ν hA).ne_top hp).symm
  intro r
  obtain ⟨a, d, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl r
  have hd : ν (algebraMap A L (d : A)) = 0 := by
    apply le_antisymm ?_ (hA d)
    apply le_of_not_gt
    intro h
    apply d.property
    exact he.le ((mem_branchCenterIdeal ν hA d).mpr h)
  have hmul := congrArg (algebraMap R L) (IsLocalization.mk'_spec R a d)
  rw [map_mul, ← IsScalarTower.algebraMap_apply A R L,
    ← IsScalarTower.algebraMap_apply A R L] at hmul
  have hv := congrArg ν hmul
  rw [ν.map_mul, hd, add_zero] at hv
  rw [hv]
  exact hA a

/-- Positive common order forces the branch to be centered at the maximal
ideal generated by those coordinates, hence regular on the localization there. -/
theorem common_base_branch_regular_at_localization {A R L ι : Type*}
    [CommRing A] [CommRing R] [Field L] [Algebra A R] [Algebra A L]
    [Algebra R L] [IsScalarTower A R L] [Fintype ι]
    (p : Ideal A) [p.IsMaximal] [IsLocalization.AtPrime R p]
    (V : ι → A) (hV : Ideal.span (Set.range V) = p)
    (ν : AddValuation L (WithTop ℤ))
    (hA : ∀ a : A, 0 ≤ ν (algebraMap A L a))
    (hpos : 0 < branchCommonZeroOrder ν (fun j => algebraMap A L (V j))) :
    ∀ r : R, 0 ≤ ν (algebraMap R L r) := by
  apply branch_order_nonnegative_on_localization p ν hA
  rw [← hV]
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  apply (mem_branchCenterIdeal ν hA _).mpr
  have h := branchCommonZeroOrder_le_coordinates ν
    (fun j => algebraMap A L (V j)) (fun j => hA (V j)) j
  exact lt_of_lt_of_le (by exact_mod_cast hpos) h

end
end PierceLengthBound.FixedDividend
