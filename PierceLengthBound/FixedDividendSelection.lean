/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.MinorHeight

/-!
# Selected orbit windows and their exact minor height

The selected starts are the good starts at gap height `28a/(AT) + 1`; they have the
support `i + 8 < P a b` used by the fixed-dividend identities. The integer floor of
the minor height bound bounds every selected minor and is positive for windows of
length at least 36.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- Gap threshold for a remainder window. -/
def selectedGapHeight (a A T : ℕ) : ℕ := 28 * a / (A * T) + 1

/-- The integer floor of the minor height bound. -/
def selectedMinorHeight (a A T : ℕ) : ℕ :=
  3609600 * A ^ 4 * selectedGapHeight a A T ^ 6 / a ^ 3

/-- Starts with seven small gaps and the necessary positive orbit support: the good starts
at the selected gap height. -/
abbrev selectedStarts (a b s T A : ℕ) : Finset ℕ := goodStarts a b s T (selectedGapHeight a A T)

/-- At least half of a window of length at least 36 consists of selected starts. -/
lemma selectedStarts_card {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hT : 36 ≤ T) :
    T ≤ 2 * (selectedStarts a b s T A).card := good_card hba hmem hsT hT

/-- Selected starts have support `i + 8 < P a b`, seven gaps between `1` and the gap
height, and `orb a b i < 2 * A`. -/
lemma selectedStart_spec {a b s T A i : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A) :
    i + 8 < P a b ∧
      (∀ m < 7, 1 ≤ kq a b (i + m) ∧ kq a b (i + m) ≤ selectedGapHeight a A T) ∧
      orb a b i < 2 * A :=
  let ⟨hP, hk, hA, _⟩ := mem_goodStarts hmem hsT hi
  ⟨hP, hk, hA⟩

/-- Every selected minor satisfies the integer height bound. -/
lemma selectedStart_minor_height {a b s T A i : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A) (t : Fin 10) :
    |plk (Mi a b i) t| ≤ (selectedMinorHeight a A T : ℤ) := by
  obtain ⟨hP, hk, hb0⟩ := selectedStart_spec hmem hsT hi
  have ha : 0 < a := by omega
  have ha3 : 0 < a ^ 3 := by positivity
  exact abs_le_div ha3 (by exact_mod_cast minor_height (A := A) hba hP hb0 hk t)

/-- The minor height bound is positive for windows of length at least 36. -/
lemma selectedMinorHeight_pos {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hT : 36 ≤ T) : 1 ≤ selectedMinorHeight a A T := by
  have hc := selectedStarts_card hba hmem hsT hT
  have hn : (selectedStarts a b s T A).Nonempty := by rw [← card_pos]; omega
  obtain ⟨i, hi⟩ := hn
  have hP := (selectedStart_spec hmem hsT hi).1
  have hL := Lz_pos (i := i + 1) hba (by omega)
  have he := congrFun (theta_eq (a := a) (b := b) i) 1
  simp only [theta, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, projθ] at he
  have hm := selectedStart_minor_height hba hmem hsT hi 6
  rw [← he, abs_of_nonneg (by omega)] at hm
  exact_mod_cast hL.trans hm

end PierceLengthBound.FixedDividend
