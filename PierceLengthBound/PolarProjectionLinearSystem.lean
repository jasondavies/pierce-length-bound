/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionAlgebra

/-! The polar base ideal and its order on every normalized branch. These
identities do not assume or compute a total base-divisor degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Matrix Finset
noncomputable section

/-- Coordinates related by an invertible matrix generate the same ideal,
over an arbitrary commutative ring. -/
theorem ideal_span_mulVec_eq {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι R) (hG : IsUnit G.det) (x : ι → R) :
    Ideal.span (Set.range (G *ᵥ x)) = Ideal.span (Set.range x) := by
  have hle (M : Matrix ι ι R) (y : ι → R) :
      Ideal.span (Set.range (M *ᵥ y)) ≤ Ideal.span (Set.range y) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change (∑ k, M j k * y k) ∈ _
    exact Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_left _ _ Ideal.mem_span_range_self)
  apply le_antisymm (hle G x)
  have hinv : G⁻¹ *ᵥ (G *ᵥ x) = x := by
    rw [mulVec_mulVec, nonsing_inv_mul G hG, one_mulVec]
  simpa only [hinv] using hle G⁻¹ (G *ᵥ x)

/-- Translating to any common zero removes the affine term of the polar map. -/
theorem polarVector_eq_centered_mulVec {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (x z : Fin 3 → R)
    (hz : polarVector ρ u v ρ' u' v' z = 0) :
    polarVector ρ u v ρ' u' v' x = polarMatrix ρ u v *ᵥ (x - z) := by
  have he : polarMatrix ρ u v *ᵥ z = -polarLinear ρ u v ρ' u' v' :=
    eq_neg_of_add_eq_zero_left hz
  simp only [polarVector, mulVec_sub, he, sub_neg_eq_add]

/-- The three polar forms generate exactly the centered coordinate ideal.
This equality holds in coordinate rings and localizations as well as polynomial rings. -/
theorem polar_baseIdeal_eq {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (hG : IsUnit (polarMatrix ρ u v).det)
    (x z : Fin 3 → R) (hz : polarVector ρ u v ρ' u' v' z = 0) :
    Ideal.span (Set.range (polarVector ρ u v ρ' u' v' x)) =
      Ideal.span (Set.range (x - z)) := by
  rw [polarVector_eq_centered_mulVec ρ u v ρ' u' v' x z hz]
  exact ideal_span_mulVec_eq _ hG _

/-- The common vanishing order of a finite coordinate family at a branch.
Unlike the pole envelope, this retains positive common orders. -/
def branchCoordinateOrder {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (x : ι → L) : WithTop ℤ :=
  Finset.univ.inf (fun j => ν (x j))

theorem le_branchCoordinateOrder_iff {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (x : ι → L) (n : WithTop ℤ) :
    n ≤ branchCoordinateOrder ν x ↔ ∀ j, n ≤ ν (x j) := by
  simp [branchCoordinateOrder, Finset.le_inf_iff]

end
end PierceLengthBound.FixedDividend
