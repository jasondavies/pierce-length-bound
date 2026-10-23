/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionAlgebra

/-! The polar quadric centered at a zero of the polar forms, over arbitrary
commutative rings: it is the centered quadratic part minus the centered linear
part. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Matrix Finset
noncomputable section

/-- The quadratic part of the centered quadric. -/
def polarCenteredQuadratic {R : Type*} [CommRing R] (ρ u v : R) (y : Fin 3 → R) : R :=
  ∑ j, y j * (polarMatrix ρ u v *ᵥ y) j

/-- The linear part of the centered quadric, with its sign reversed. -/
def polarCenteredLinear {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (y : Fin 3 → R) : R :=
  ∑ j, y j * polarLinear ρ u v ρ' u' v' j

lemma map_polarVector {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (ρ u v ρ' u' v' : R) (x : Fin 3 → R) :
    (fun j => φ (polarVector ρ u v ρ' u' v' x j)) =
      polarVector (φ ρ) (φ u) (φ v) (φ ρ') (φ u') (φ v') (fun j => φ (x j)) := by
  funext j
  fin_cases j <;> simp [polarVector, polarMatrix, polarLinear, dotProduct, Fin.sum_univ_succ]

/-- Centering at a zero of the polar forms gives the same quadric identity
over arbitrary commutative rings, including rings of formal power series. -/
theorem polar_centered_quadric_of_base {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (z y : Fin 3 → R)
    (hz : polarVector ρ u v ρ' u' v' z = 0) :
    (∑ j, (z + y) j * polarVector ρ u v ρ' u' v' (z + y) j) =
      polarCenteredQuadratic ρ u v y - polarCenteredLinear ρ u v ρ' u' v' y := by
  have he := polarQuadric_translate ρ u v ρ' u' v' 1 z y
  have hg : polarMatrix ρ u v *ᵥ z = -polarLinear ρ u v ρ' u' v' :=
    eq_neg_of_add_eq_zero_left hz
  have hg' (j : Fin 3) :
      2 * (polarMatrix ρ u v *ᵥ z) j + polarLinear ρ u v ρ' u' v' j =
        -polarLinear ρ u v ρ' u' v' j := by
    rw [hg]
    simp only [Pi.neg_apply]
    ring
  simp only [one_mul, one_smul, one_pow, hz, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, hg', mul_neg, Finset.sum_neg_distrib] at he
  simp only [Pi.add_apply]
  rw [he]
  unfold polarCenteredQuadratic polarCenteredLinear
  ring

end
end PierceLengthBound.FixedDividend
