/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendCount
public import PierceLengthBound.FixedDividendGlobalReduction

/-!
# From selected orbit starts to distinct gap counts

This connects the actual selected orbit sets, quartic multiplicity and minor heights:
each pair of a pattern and a gap vector comes from at most four selected starts.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- The selected exact minor height lies in a fixed polynomial range. -/
lemma selectedMinorHeight_le {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hT : 36 ≤ T) : selectedMinorHeight a A T ≤ 10 ^ 16 * a ^ 7 := by
  have ha : 0 < a := by omega
  have hH : selectedGapHeight a A T ≤ 29 * a := by
    unfold selectedGapHeight
    have := Nat.div_le_self (28 * a) (A * T)
    omega
  have hA : A ≤ a := by
    have := (hmem 0 (by omega)).1
    have := (orb_le a b (s + 0)).trans hba.le
    omega
  apply Nat.le_of_mul_le_mul_right (c := a ^ 3) ?_ (by positivity)
  calc selectedMinorHeight a A T * a ^ 3 ≤
      3609600 * A ^ 4 * selectedGapHeight a A T ^ 6 := Nat.div_mul_le_self _ _
    _ ≤ 3609600 * a ^ 4 * (29 * a) ^ 6 := by gcongr
    _ = 2147074259481600 * a ^ 7 * a ^ 3 := by ring
    _ ≤ (10 ^ 16 * a ^ 7) * a ^ 3 := by gcongr; norm_num

/-- Each pair of a pattern and a gap vector comes from at most four selected starts. -/
theorem selectedStarts_card_le_pair_image {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b) :
    (selectedStarts a b s T A).card ≤
      4 * ((selectedStarts a b s T A).image fun i => (plk (Mi a b i), kap a b i)).card := by
  have facts := fun i hi => selectedStart_spec hmem hsT (i := i) hi
  apply pattern_gap_multiplicity (θ := theta a b) (Q := fun i => (qq a b i : ℤ))
    (a := (a : ℤ)) (fun i _ => theta_eq i)
  · intro i hi i' hi' h
    have hP := (facts i hi).1
    have hP' := (facts i' hi').1
    simp only [Nat.cast_inj] at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h.symm
  · intro i hi
    simpa [theta] using Lz_pos hba (i := i) (by have := (facts i hi).1; omega)
  · intro i hi
    simpa [theta, kap] using mult_at (a := a) (b := b) (i := i)
      (by have := (facts i hi).1; omega)

/-- At least `T/8` pairs of a pattern and a gap vector occur among the selected starts. -/
theorem le_eight_mul_pair_image {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hT : 36 ≤ T) :
    T ≤ 8 * ((selectedStarts a b s T A).image fun i => (plk (Mi a b i), kap a b i)).card := by
  have h1 := selectedStarts_card hba hmem hsT hT
  have h2 := selectedStarts_card_le_pair_image hba hmem hsT
  omega

end PierceLengthBound.FixedDividend
