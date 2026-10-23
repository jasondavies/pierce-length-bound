/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSievePatternCount
public import PierceLengthBound.PolarProjectionCountAssembly

/-! Absorb the completion logarithm on the actual polynomial-sized orbit
windows. The vertex sieve and the geometric count have matching interfaces. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

open Classical in
theorem selected_branch_pattern_count_slow
    (good : ℕ → (Fin 4 → ℤ) → Prop) {R : ℕ → ℕ} (hR : SlowGrowth R)
    (hcount : ∀ a : ℕ, 0 < a → ∀ g B : ℕ,
      0 < g → g ≤ 2 * (10 ^ 16 * a ^ 7) → 0 < B → B ≤ 2 * (10 ^ 16 * a ^ 7) →
      (((ibox4 B).filter fun x => ¬good a (fun i => (g : ℤ) * x i)).card : ℝ) ≤
        R a * (B : ℝ) ^ (7 / 2 : ℝ)) :
    ∃ Rbad : ℕ → ℕ, SlowGrowth Rbad ∧
      PolarBadPatternCount (fun a p => good a (branchFirstVertex p)) Rbad := by
  obtain ⟨K, hK, hbound⟩ := branch_full_pattern_count
  let Kn : ℕ := ⌈K⌉₊
  refine ⟨fun a => Kn * R a * (Nat.log 2 (10 ^ 16 * a ^ 7) + 1),
    ((slowGrowth_const Kn).mul hR).mul (polynomial_log_slow (10 ^ 16) 7), ?_⟩
  intro a b s T A hba hmem hsT hT
  let X := selectedMinorHeight a A T
  let S := ((selectedStarts a b s T A).image (fun i => plk (Mi a b i))).filter
    fun p => ¬good a (branchFirstVertex p)
  have hX : 0 < X := selectedMinorHeight_pos hba hmem hsT hT
  have hXB : X ≤ 10 ^ 16 * a ^ 7 := selectedMinorHeight_le hba hmem hT
  have hc : (S.card : ℝ) ≤ K * R a * (X : ℝ) ^ (9 / 2 : ℝ) * (Nat.log 2 X + 1 : ℕ) := by
    apply hbound (fun x => ¬good a x) (R a) (by positivity) X hX S
    · intro p hp
      obtain ⟨hp, hbadp⟩ := mem_filter.mp hp
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      refine ⟨selectedStart_minor_height hba hmem hsT hi, plucker _, ?_, hbadp⟩
      intro hz
      have hp0 := orbit_pattern_first (l := i) hba
        (by have := (selectedStart_spec hmem hsT hi).1; omega)
      apply hp0
      exact congrFun hz 0
    · intro g B hg hgX hB hBX
      convert hcount a (by omega) g B hg (hgX.trans (Nat.mul_le_mul_left 2 hXB))
        hB (hBX.trans (Nat.mul_le_mul_left 2 hXB)) using 1
      apply congrArg (fun V : Finset (Fin 4 → ℤ) => (V.card : ℝ))
      ext x
      simp only [mem_filter]
  have hlog : Nat.log 2 X + 1 ≤ Nat.log 2 (10 ^ 16 * a ^ 7) + 1 := by
    exact Nat.add_le_add_right (Nat.log_mono_right hXB) 1
  have hpow : (X : ℝ) ^ (9 / 2 : ℝ) ≤ (X : ℝ) ^ (14 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX) (by norm_num)
  have hKn : K ≤ (Kn : ℝ) := Nat.le_ceil K
  change (S.card : ℝ) ≤ _
  push_cast
  calc
    _ ≤ K * R a * (X : ℝ) ^ (9 / 2 : ℝ) * (Nat.log 2 X + 1 : ℕ) := hc
    _ ≤ (Kn : ℝ) * R a * (X : ℝ) ^ (14 / 3 : ℝ) *
        (Nat.log 2 (10 ^ 16 * a ^ 7) + 1 : ℕ) := by gcongr
    _ = _ := by dsimp [X]; push_cast; ring

end
end PierceLengthBound.FixedDividend
