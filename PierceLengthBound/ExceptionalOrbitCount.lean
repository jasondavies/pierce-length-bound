/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ExceptionalMinorChanges
public import PierceLengthBound.FixedDividendParity
public import PierceLengthBound.FixedDividendSelection

/-! Exceptional-pattern counting on actual selected orbit windows. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- The normalized exceptional relations give exactly the integer minor cuts. -/
theorem exceptional_minor_relation_of_ratios {p : Fin 10 → ℤ} (hp : p 0 ≠ 0) (d : Fin 4)
    (h : exceptionalRelation ((p 6 : ℝ) / p 0) ((p 3 : ℝ) / p 0) (-(p 1 : ℝ) / p 0) d) :
    ExceptionalMinorRelation p d := by
  have hpR : (p 0 : ℝ) ≠ 0 := by exact_mod_cast hp
  fin_cases d <;> norm_num [exceptionalRelation, ExceptionalMinorRelation] at h ⊢
  all_goals field_simp [hpR] at h
  all_goals norm_cast at h
  all_goals omega

/-- Exceptional patterns in a finite set of actual integer matrices. -/
theorem exceptional_matrix_pattern_count {ι : Type*} (G : Finset ι)
    (M : ι → Fin 3 → Fin 5 → ℤ) {X : ℕ} (hX : 1 ≤ X)
    (hheight : ∀ i ∈ G, ∀ j, |plk (M i) j| ≤ X) :
    ((G.image (fun i => plk (M i))).filter fun p => ∃ d, ExceptionalMinorRelation p d).card ≤
      4 * ((6 * X + 1) ^ 3 + (Nat.log 2 (3 * X) + 1) * (273375 * (3 * X) ^ 4)) := by
  classical
  apply exceptional_minor_vector_count hX
  intro p hp
  obtain ⟨hp, hd⟩ := mem_filter.mp hp
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
  exact ⟨hheight i hi, ⟨M i, rfl⟩, hd⟩

/-- Exact exceptional-pattern count in the selected remainder window. -/
theorem selected_exceptional_pattern_count {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hT : 36 ≤ T) :
    let X := selectedMinorHeight a A T
    (((selectedStarts a b s T A).image (fun i => plk (Mi a b i))).filter
      fun p => ∃ d, ExceptionalMinorRelation p d).card ≤
      4 * ((6 * X + 1) ^ 3 + (Nat.log 2 (3 * X) + 1) * (273375 * (3 * X) ^ 4)) := by
  classical
  exact exceptional_matrix_pattern_count (selectedStarts a b s T A) (Mi a b)
    (selectedMinorHeight_pos hba hmem hsT hT)
    (fun i hi j => selectedStart_minor_height hba hmem hsT hi j)

/-- Every exceptional actual orbit pattern satisfies one of the counted minor cuts. -/
theorem orbit_exceptional_minor_relation {a b i : ℕ} (hba : b < a)
    (hi : i + 6 < P a b)
    (hne : ¬NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i)) :
    ∃ d, ExceptionalMinorRelation (plk (Mi a b i)) d := by
  classical
  unfold NonexceptionalPattern at hne
  push Not at hne
  obtain ⟨d, hd⟩ := hne
  have h0 := congrFun (theta_eq (a := a) (b := b) i) 0
  have h6 := congrFun (theta_eq (a := a) (b := b) i) 1
  have h3 := congrFun (theta_eq (a := a) (b := b) i) 3
  have h1 := congrFun (theta_eq (a := a) (b := b) i) 4
  norm_num [theta, projθ] at h0 h6 h3 h1
  have hL := Lz_pos hba (i := i) (by omega)
  refine ⟨d, exceptional_minor_relation_of_ratios (by omega) d ?_⟩
  simpa only [patternRho, patternU, patternV, h0, h6, h3, h1, Int.cast_neg] using hd

end PierceLengthBound.FixedDividend
