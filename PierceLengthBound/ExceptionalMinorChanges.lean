/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ExceptionalZeroMinorCount

/-! Bounded integral column changes for the four exceptional minor relations.
The induced maps are injective on complete minor vectors, preserving common factors. -/

@[expose] public section
namespace PierceLengthBound
open Finset

/-- The four exceptional relations, in the ten-minor indexing used by this project. -/
def ExceptionalMinorRelation (p : Fin 10 → ℤ) (d : Fin 4) : Prop :=
  ![p 6 - p 1 - p 0, p 6 - p 1, p 3 - p 0, p 0 - p 6 - p 3] d = 0

instance (p : Fin 10 → ℤ) (d : Fin 4) : Decidable (ExceptionalMinorRelation p d) := by
  unfold ExceptionalMinorRelation
  infer_instance

/-- Explicit column changes, with the exceptional determinant in the first position. -/
def exceptionalColumnChange (d : Fin 4) (M : Fin 3 → Fin 5 → ℤ) : Fin 3 → Fin 5 → ℤ :=
  fun i => ![![M i 1, M i 2 + M i 0, M i 3 - M i 0, M i 0, M i 4],
    ![M i 1, M i 2 + M i 0, M i 3, M i 0, M i 4],
    ![M i 0, M i 2, M i 3 + M i 1, M i 1, M i 4],
    ![M i 0 + M i 1, M i 2, -M i 1 - M i 3, M i 1, M i 4]] d

/-- Induced integral linear transformations on all ten minors. -/
def exceptionalMinorChange (d : Fin 4) (p : Fin 10 → ℤ) : Fin 10 → ℤ :=
  ![![-p 0 - p 1 + p 6, p 0, -p 2 + p 7, p 1, p 2 + p 8, -p 2,
       p 3, p 4 + p 5 + p 9, -p 4, -p 5],
    ![-p 1 + p 6, p 0, -p 2 + p 7, p 1, p 8, -p 2, p 3, p 5 + p 9, -p 4, -p 5],
    ![-p 0 + p 3, -p 0, p 4, -p 1, p 2 + p 5, p 2, p 6, -p 7 + p 9, -p 7, -p 8],
    ![p 0 - p 3 - p 6, -p 0, p 4 + p 7, p 1, -p 2 - p 5 - p 8, p 2,
       -p 6, p 7 - p 9, -p 7, p 8]] d

/-- Explicit inverse transformations; in particular no common factors are discarded. -/
def exceptionalMinorInverse (d : Fin 4) (p : Fin 10 → ℤ) : Fin 10 → ℤ :=
  ![![p 1, p 3, -p 5, p 6, -p 8, -p 9, p 0 + p 1 + p 3,
       p 2 - p 5, p 4 + p 5, p 7 + p 8 + p 9],
    ![p 1, p 3, -p 5, p 6, -p 8, -p 9, p 0 + p 3, p 2 - p 5, p 4, p 7 + p 9],
    ![-p 1, -p 3, p 5, p 0 - p 1, p 2, p 4 - p 5, p 6, -p 8, -p 9, p 7 - p 8],
    ![-p 1, p 3, p 5, -p 0 - p 1 + p 6, p 2 + p 8, -p 4 - p 5 - p 9,
       -p 6, -p 8, p 9, -p 7 - p 8]] d

theorem exceptionalMinorInverse_left (d : Fin 4) (p : Fin 10 → ℤ) :
    exceptionalMinorInverse d (exceptionalMinorChange d p) = p := by
  funext j
  fin_cases d <;> fin_cases j <;> norm_num [exceptionalMinorInverse, exceptionalMinorChange] <;> ring

theorem exceptionalMinorChange_injective (d : Fin 4) :
    Function.Injective (exceptionalMinorChange d) := by
  intro p q h
  have := congrArg (exceptionalMinorInverse d) h
  simpa only [exceptionalMinorInverse_left] using this

/-- These ten-coordinate maps are the minors of the actual changed matrix. -/
theorem plk_exceptionalColumnChange (d : Fin 4) (M : Fin 3 → Fin 5 → ℤ) :
    plk (exceptionalColumnChange d M) = exceptionalMinorChange d (plk M) := by
  funext j
  fin_cases d <;> fin_cases j <;>
    norm_num [plk, trip, minor3, exceptionalColumnChange, exceptionalMinorChange] <;> ring

theorem exceptionalMinorChange_zero {d : Fin 4} {p : Fin 10 → ℤ}
    (h : ExceptionalMinorRelation p d) : exceptionalMinorChange d p 0 = 0 := by
  fin_cases d <;> norm_num [ExceptionalMinorRelation, exceptionalMinorChange] at h ⊢ <;>
    linear_combination h

/-- The height increases by at most three, uniformly across all four changes. -/
theorem exceptionalMinorChange_height {X : ℕ} {p : Fin 10 → ℤ}
    (hp : ∀ j, |p j| ≤ X) (d : Fin 4) : ∀ j, |exceptionalMinorChange d p j| ≤ 3 * X := by
  have h0 := abs_le.mp (hp 0)
  have h1 := abs_le.mp (hp 1)
  have h2 := abs_le.mp (hp 2)
  have h3 := abs_le.mp (hp 3)
  have h4 := abs_le.mp (hp 4)
  have h5 := abs_le.mp (hp 5)
  have h6 := abs_le.mp (hp 6)
  have h7 := abs_le.mp (hp 7)
  have h8 := abs_le.mp (hp 8)
  have h9 := abs_le.mp (hp 9)
  intro j
  fin_cases d <;> fin_cases j <;> norm_num [exceptionalMinorChange] <;>
    rw [abs_le] <;> constructor <;> omega

/-- Count one actual exceptional relation by an injective bounded column change. -/
theorem exceptional_relation_count {S : Finset (Fin 10 → ℤ)} {X : ℕ} (hX : 1 ≤ X)
    (d : Fin 4) (hS : ∀ p ∈ S, (∀ j, |p j| ≤ X) ∧
      (∃ M : Fin 3 → Fin 5 → ℤ, plk M = p) ∧ ExceptionalMinorRelation p d) :
    S.card ≤ (6 * X + 1) ^ 3 + (Nat.log 2 (3 * X) + 1) * (273375 * (3 * X) ^ 4) := by
  classical
  have h := zero_minor_vector_count (S := S.image (exceptionalMinorChange d))
    (X := 3 * X) (by omega) (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      obtain ⟨hb, ⟨M, hM⟩, hd⟩ := hS p hp
      refine ⟨?_, ?_, exceptionalMinorChange_zero hd⟩
      · simpa only [Nat.cast_mul, Nat.cast_ofNat] using exceptionalMinorChange_height hb d
      · rw [← hM, ← plk_exceptionalColumnChange]
        exact plucker _)
  rw [card_image_of_injective _ (exceptionalMinorChange_injective d)] at h
  convert h using 1; ring

/-- The complete exceptional-pattern estimate, including every common divisor. -/
theorem exceptional_minor_vector_count {S : Finset (Fin 10 → ℤ)} {X : ℕ} (hX : 1 ≤ X)
    (hS : ∀ p ∈ S, (∀ j, |p j| ≤ X) ∧
      (∃ M : Fin 3 → Fin 5 → ℤ, plk M = p) ∧ ∃ d, ExceptionalMinorRelation p d) :
    S.card ≤ 4 * ((6 * X + 1) ^ 3 +
      (Nat.log 2 (3 * X) + 1) * (273375 * (3 * X) ^ 4)) := by
  classical
  have hsub : S ⊆ univ.biUnion (fun d : Fin 4 => S.filter fun p => ExceptionalMinorRelation p d) := by
    intro p hp
    obtain ⟨d, hd⟩ := (hS p hp).2.2
    exact mem_biUnion.mpr ⟨d, mem_univ _, mem_filter.mpr ⟨hp, hd⟩⟩
  calc S.card ≤ (univ.biUnion (fun d : Fin 4 => S.filter fun p => ExceptionalMinorRelation p d)).card :=
        card_le_card hsub
    _ ≤ ∑ d : Fin 4, (S.filter fun p => ExceptionalMinorRelation p d).card := card_biUnion_le
    _ ≤ ∑ _d : Fin 4, ((6 * X + 1) ^ 3 +
        (Nat.log 2 (3 * X) + 1) * (273375 * (3 * X) ^ 4)) := by
      apply sum_le_sum
      intro d _
      exact exceptional_relation_count hX d (by
        intro p hp
        obtain ⟨hp, hd⟩ := mem_filter.mp hp
        exact ⟨(hS p hp).1, (hS p hp).2.1, hd⟩)
    _ = _ := by simp

end PierceLengthBound
