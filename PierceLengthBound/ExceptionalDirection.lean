/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ExceptionalPlaneCount

/-! Primitive common directions for rank-one pairs of integer vectors. -/

@[expose] public section
namespace PierceLengthBound
open Finset
open scoped Matrix
open Matrix (vec3_dotProduct)

/-- A primitive vector's integral collinear vectors are integral multiples. -/
theorem integral_multiple_of_primitive {z b c : Fin 3 → ℤ}
    (hc : c ⬝ᵥ z = 1) (hcross : ∀ j, (z ⨯₃ b) j = 0) :
    ∀ j, b j = c ⬝ᵥ b * z j := by
  have h0 := hcross 0
  have h1 := hcross 1
  have h2 := hcross 2
  rw [cross_apply_zero] at h0
  rw [cross_apply_one] at h1
  rw [cross_apply_two] at h2
  simp only [vec3_dotProduct] at hc ⊢
  intro j
  fin_cases j
  · change b 0 = _ * z 0
    linear_combination -b 0 * hc - c 1 * h2 + c 2 * h1
  · change b 1 = _ * z 1
    linear_combination -b 1 * hc + c 0 * h2 - c 2 * h0
  · change b 2 = _ * z 2
    linear_combination -b 2 * hc - c 0 * h1 + c 1 * h0

/-- Divide a nonzero vector by the gcd of all its coordinates, retaining Bézout data. -/
theorem exists_primitive_direction {a : Fin 3 → ℤ} (ha : a ≠ 0) :
    ∃ (g : ℕ) (z c : Fin 3 → ℤ), 0 < g ∧
      (∀ j, a j = (g : ℤ) * z j) ∧ c ⬝ᵥ z = 1 := by
  let g := gcd4 0 a
  have hg : 0 < g := by
    by_contra h
    have hz : g = 0 := by omega
    apply ha
    funext j
    have hd := gcd4_dvd 0 a j
    change (g : ℤ) ∣ a j at hd
    rw [hz, Nat.cast_zero, zero_dvd_iff] at hd
    exact hd
  have hd : ∀ j, ∃ z : ℤ, a j = (g : ℤ) * z := fun j => gcd4_dvd 0 a j
  choose z hz using hd
  obtain ⟨e, c0, c1, c2, hb⟩ := gcd4_bezout 0 a
  let c : Fin 3 → ℤ := ![c0, c1, c2]
  refine ⟨g, z, c, hg, hz, ?_⟩
  have he : (g : ℤ) * c ⬝ᵥ z = (g : ℤ) * 1 := by
    simp only [Nat.cast_zero, zero_mul, zero_add] at hb
    rw [hz 0, hz 1, hz 2] at hb
    rw [vec3_dotProduct]
    dsimp [c]
    linear_combination hb
  exact mul_left_cancel₀ (by exact_mod_cast hg.ne' : (g : ℤ) ≠ 0) he

/-- Every nonzero rank-one pair, including nonprimitive pairs, has a common
primitive integral direction. -/
theorem exists_common_primitive_direction {a b : Fin 3 → ℤ}
    (hne : a ≠ 0 ∨ b ≠ 0) (hcross : ∀ j, (a ⨯₃ b) j = 0) :
    ∃ (z c : Fin 3 → ℤ) (r s : ℤ), c ⬝ᵥ z = 1 ∧
      (∀ j, a j = r * z j) ∧ (∀ j, b j = s * z j) ∧ (r ≠ 0 ∨ s ≠ 0) := by
  have step {a b : Fin 3 → ℤ} (ha : a ≠ 0) (hab : ∀ j, (a ⨯₃ b) j = 0) :
      ∃ (z c : Fin 3 → ℤ) (r s : ℤ), c ⬝ᵥ z = 1 ∧
        (∀ j, a j = r * z j) ∧ (∀ j, b j = s * z j) ∧ r ≠ 0 := by
    obtain ⟨g, z, c, hg, hz, hc⟩ := exists_primitive_direction ha
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
    have hzb : ∀ j, (z ⨯₃ b) j = 0 := by
      intro j
      apply mul_left_cancel₀ hg0
      have h := hab j
      simp only [cross_apply_cyc, hz] at h ⊢
      linear_combination h
    exact ⟨z, c, g, c ⬝ᵥ b, hc, hz, integral_multiple_of_primitive hc hzb, hg0⟩
  rcases hne with ha | hb
  · obtain ⟨z, c, r, s, hc, ha, hb, hr⟩ := step ha hcross
    exact ⟨z, c, r, s, hc, ha, hb, Or.inl hr⟩
  · have hba : ∀ j, (b ⨯₃ a) j = 0 := by
      intro j
      have h := hcross j
      simp only [cross_apply_cyc] at h ⊢
      linear_combination -h
    obtain ⟨z, c, s, r, hc, hb, ha, hs⟩ := step hb hba
    exact ⟨z, c, r, s, hc, ha, hb, Or.inr hs⟩

/-- Orthogonality to a nonzero pair passes to its common primitive direction. -/
theorem common_direction_orthogonal {a b z t : Fin 3 → ℤ} {r s : ℤ}
    (ha : ∀ j, a j = r * z j) (hb : ∀ j, b j = s * z j)
    (hne : r ≠ 0 ∨ s ≠ 0) (hat : a ⬝ᵥ t = 0) (hbt : b ⬝ᵥ t = 0) :
    z ⬝ᵥ t = 0 := by
  rcases hne with hr | hs
  · apply mul_left_cancel₀ hr
    simp only [vec3_dotProduct, ha] at hat ⊢
    linear_combination hat
  · apply mul_left_cancel₀ hs
    simp only [vec3_dotProduct, hb] at hbt ⊢
    linear_combination hbt

end PierceLengthBound
