/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendWindow

/-!
# Selected orbit windows and their exact minor height

The existing selection lemma already supplies the support length needed by the
fixed-dividend identities. The integer floor of the minor bound is positive
whenever a selected window exists; no additive height rounding loss is necessary.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- Gap threshold for a remainder window. -/
def selectedGapHeight (a A T : ℕ) : ℕ := 28 * a / (A * T) + 1

/-- Exact integral minor height, without an added unit. -/
def selectedMinorHeight (a A T : ℕ) : ℕ :=
  3609600 * A ^ 4 * selectedGapHeight a A T ^ 6 / a ^ 3

/-- Starts with seven small gaps and the necessary positive orbit support. -/
def selectedStarts (a b s T A : ℕ) : Finset ℕ :=
  (Ico s (s + T)).filter fun i => i + 9 ≤ s + T ∧
    ∀ m ∈ range 7, kq a b (i + m) ≤ (selectedGapHeight a A T : ℤ)

lemma selectedStarts_card {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hT : 36 ≤ T) :
    T ≤ 2 * (selectedStarts a b s T A).card := good_card hba hmem hsT hT

lemma selectedStart_spec {a b s T A i : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A) :
    i + 8 < P a b ∧
      (∀ m < 7, 1 ≤ kq a b (i + m) ∧ kq a b (i + m) ≤ selectedGapHeight a A T) ∧
      orb a b i < 2 * A := by
  obtain ⟨hiI, h9, hk⟩ := mem_filter.mp hi
  have := mem_Ico.mp hiI
  refine ⟨by omega, fun m hm => ⟨kq_pos (by omega), hk m (mem_range.mpr hm)⟩, ?_⟩
  have := (hmem (i - s) (by omega)).2
  rwa [show s + (i - s) = i by omega] at this

/-- Every selected minor satisfies the unrounded integer height bound. -/
lemma selectedStart_minor_height {a b s T A i : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A) (t : Fin 10) :
    |plk (Mi a b i) t| ≤ (selectedMinorHeight a A T : ℤ) := by
  obtain ⟨hP, hk, hb0⟩ := selectedStart_spec hmem hsT hi
  have ha : 0 < a := by omega
  have ha3 : 0 < a ^ 3 := by positivity
  exact abs_le_div ha3 (by exact_mod_cast minor_height (A := A) hba hP hb0 hk t)

/-- A represented minor pattern has a positive exact height bound. -/
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
