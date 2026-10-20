/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ExceptionalDirection

/-! The uniform count on one dyadic range of primitive directions. -/

@[expose] public section
namespace PierceLengthBound
open Finset
noncomputable section

/-- Primitive directions with a coordinate between `Z` and the ambient height. -/
def exceptionalNormals (X Z : ℕ) : Finset (Fin 3 → ℤ) := by
  classical
  exact (ibox3 (2 * Z)).filter fun z =>
    (∃ c, dot3 c z = 1) ∧ ∃ j, Z ≤ (z j).natAbs ∧ (z j).natAbs ≤ X

/-- Two scalar multiples of a primitive direction. -/
def exceptionalScalars (X Z : ℕ) : Finset (ℤ × ℤ) :=
  Icc (-(X / Z : ℕ) : ℤ) (X / Z : ℕ) ×ˢ Icc (-(X / Z : ℕ) : ℤ) (X / Z : ℕ)

/-- Integer points in the plane normal to `z`. -/
def exceptionalPlane (X : ℕ) (z : Fin 3 → ℤ) : Finset (Fin 3 → ℤ) :=
  (ibox3 X).filter fun t => dot3 z t = 0

/-- Parameter tuples for one dyadic range. -/
def exceptionalParameters (X Z : ℕ) :
    Finset ((Fin 3 → ℤ) × (ℤ × ℤ) × (Fin 3 → ℤ)) := by
  classical
  exact (exceptionalNormals X Z).biUnion fun z =>
    (exceptionalScalars X Z ×ˢ exceptionalPlane X z).image fun p => (z, p)

lemma ibox3_card (X : ℕ) : (ibox3 X).card = (2 * X + 1) ^ 3 := by
  have hi : (Icc (-(X : ℤ)) X).card = 2 * X + 1 := by rw [Int.card_Icc]; omega
  rw [ibox3, Fintype.card_piFinset, Fin.prod_univ_three, hi]
  ring

/-- Each dyadic primitive-direction range contributes at most an absolute
constant times `X⁴`, including nonprimitive scalar multiples. -/
theorem exceptional_parameters_count {X Z : ℕ} (hZ : 1 ≤ Z) (hZX : Z ≤ X) :
    (exceptionalParameters X Z).card ≤ 273375 * X ^ 4 := by
  classical
  have hnormal : (exceptionalNormals X Z).card ≤ 125 * Z ^ 3 := by
    calc (exceptionalNormals X Z).card ≤ (ibox3 (2 * Z)).card := card_filter_le ..
      _ = (4 * Z + 1) ^ 3 := by rw [ibox3_card]; congr 1; ring
      _ ≤ (5 * Z) ^ 3 := Nat.pow_le_pow_left (by omega) _
      _ = _ := by ring
  have hq : 1 ≤ X / Z := Nat.div_pos hZX (by omega)
  have hscalar : (exceptionalScalars X Z).card ≤ 9 * (X / Z) ^ 2 := by
    have he : (exceptionalScalars X Z).card = (2 * (X / Z) + 1) ^ 2 := by
      have hi : (Icc (-(X / Z : ℕ) : ℤ) (X / Z : ℕ)).card = 2 * (X / Z) + 1 := by
        rw [Int.card_Icc]; omega
      rw [exceptionalScalars, card_product, hi, pow_two]
    rw [he]
    nlinarith
  have hplane (z : Fin 3 → ℤ) (hz : z ∈ exceptionalNormals X Z) :
      Z * (exceptionalPlane X z).card ≤ 243 * X ^ 2 := by
    obtain ⟨_, ⟨c, hc⟩, j, hj, hjX⟩ := mem_filter.mp hz
    calc Z * (exceptionalPlane X z).card ≤ (z j).natAbs * (exceptionalPlane X z).card := Nat.mul_le_mul_right _ hj
      _ ≤ 243 * X ^ 2 := primitive_plane_count z c hc j (by omega) hjX (by
        intro t ht
        obtain ⟨ht, he⟩ := mem_filter.mp ht
        exact ⟨fun k => abs_le.mpr (mem_Icc.mp (Fintype.mem_piFinset.mp ht k)), he⟩)
  have hp : (exceptionalParameters X Z).card ≤
      ∑ z ∈ exceptionalNormals X Z,
        (exceptionalScalars X Z).card * (exceptionalPlane X z).card := by
    unfold exceptionalParameters
    exact card_biUnion_le.trans (sum_le_sum fun z _ =>
      card_image_le.trans_eq (card_product _ _))
  have hb : Z * (exceptionalParameters X Z).card ≤
      125 * Z ^ 3 * (9 * (X / Z) ^ 2) * (243 * X ^ 2) := by
    calc Z * (exceptionalParameters X Z).card ≤ Z *
        ∑ z ∈ exceptionalNormals X Z,
          (exceptionalScalars X Z).card * (exceptionalPlane X z).card := Nat.mul_le_mul_left Z hp
      _ = ∑ z ∈ exceptionalNormals X Z,
          (exceptionalScalars X Z).card * (Z * (exceptionalPlane X z).card) := by
        rw [mul_sum]; apply sum_congr rfl; intro z _; ring
      _ ≤ ∑ _z ∈ exceptionalNormals X Z,
          (9 * (X / Z) ^ 2) * (243 * X ^ 2) := by
        apply sum_le_sum; intro z hz
        exact Nat.mul_le_mul hscalar (hplane z hz)
      _ = (exceptionalNormals X Z).card * (9 * (X / Z) ^ 2) * (243 * X ^ 2) := by
        rw [sum_const, smul_eq_mul]; ring
      _ ≤ _ := by gcongr
  have hdiv : Z * (X / Z) ≤ X := by simpa [mul_comm] using Nat.div_mul_le_self X Z
  exact Nat.le_of_mul_le_mul_left (by
    calc Z * (exceptionalParameters X Z).card ≤
        125 * Z ^ 3 * (9 * (X / Z) ^ 2) * (243 * X ^ 2) := hb
      _ = 273375 * Z * (Z * (X / Z)) ^ 2 * X ^ 2 := by ring
      _ ≤ 273375 * Z * X ^ 2 * X ^ 2 := by gcongr
      _ = Z * (273375 * X ^ 4) := by ring) (by omega)

end
end PierceLengthBound
