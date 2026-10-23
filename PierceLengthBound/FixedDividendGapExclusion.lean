/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendIdentity
public import PierceLengthBound.FixedDividendLines
public import PierceLengthBound.PatternBound

/-!
# Large gaps exclude the four line obstructions

The existing Newton-basis Gram upper bound already has the required Vandermonde
leading term. It suffices here, without a new expansion of raw Hankel determinants.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

variable {a b : ℕ}

lemma gramP_le_middle_gaps {k0 k1 k2 k3 k4 H : ℤ}
    (h0 : 1 ≤ k0) (h1 : 1 ≤ k1) (h2 : 1 ≤ k2) (h3 : 1 ≤ k3) (h4 : 1 ≤ k4)
    (g0 : k0 ≤ H) (g1 : k1 ≤ H) (g2 : k2 ≤ H) (g3 : k3 ≤ H) (g4 : k4 ≤ H) :
    gramP k0 k1 k2 k3 k4 ≤ H ^ 5 * (12 * k1 + 464) ∧
      gramP k0 k1 k2 k3 k4 ≤ H ^ 5 * (12 * k2 + 464) := by
  have hH : 0 ≤ H := by omega
  have hΔ := delta_left_le h0 h1 h2 g0 g1 g2
  have hg := gramP_le h0 h1 h2 h3 h4 g0 g1 g2 g3 g4
  have h12 : k1 * k2 * (k1 + k2) ≤ k1 * H * (2 * H) := by gcongr; omega
  have h21 : k1 * k2 * (k1 + k2) ≤ H * k2 * (2 * H) := by gcongr; omega
  have h12' := mul_le_mul_of_nonneg_left h12 (by positivity : 0 ≤ 6 * H ^ 3)
  have h21' := mul_le_mul_of_nonneg_left h21 (by positivity : 0 ≤ 6 * H ^ 3)
  constructor <;> nlinarith

/-- A quantitative version of the candidate's large-scale condition. -/
theorem middle_gaps_large {a Q X H k0 k1 k2 k3 k4 : ℤ}
    (ha : 0 < a) (h0 : 1 ≤ k0) (h1 : 1 ≤ k1) (h2 : 1 ≤ k2) (h3 : 1 ≤ k3) (h4 : 1 ≤ k4)
    (g0 : k0 ≤ H) (g1 : k1 ≤ H) (g2 : k2 ≤ H) (g3 : k3 ≤ H) (g4 : k4 ≤ H)
    (hlabel : Q ^ 4 ≤ a * gramP k0 k1 k2 k3 k4)
    (hscale : a * H ^ 5 * (24 * X + 464) < Q ^ 4) :
    2 * X < k1 ∧ 2 * X < k2 := by
  have hg := gramP_le_middle_gaps h0 h1 h2 h3 h4 g0 g1 g2 g3 g4
  have hH : 0 ≤ H := by omega
  constructor
  · by_contra hn
    have hk : k1 ≤ 2 * X := by omega
    have hbound : gramP k0 k1 k2 k3 k4 ≤ H ^ 5 * (24 * X + 464) :=
      hg.1.trans (mul_le_mul_of_nonneg_left (by omega) (by positivity))
    have := mul_le_mul_of_nonneg_left hbound ha.le
    nlinarith
  · by_contra hn
    have hk : k2 ≤ 2 * X := by omega
    have hbound : gramP k0 k1 k2 k3 k4 ≤ H ^ 5 * (24 * X + 464) :=
      hg.2.trans (mul_le_mul_of_nonneg_left (by omega) (by positivity))
    have := mul_le_mul_of_nonneg_left hbound ha.le
    nlinarith

/-- The label inequality with the positive integer label removed. -/
lemma orbit_gram_lower (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    (qq a b i : ℤ) ^ 4 ≤ (a : ℤ) * gramP (kq a b i) (kq a b (i + 1))
      (kq a b (i + 2)) (kq a b (i + 3)) (kq a b (i + 4)) := by
  have hl : Lz a b i * (qq a b i : ℤ) ^ 4 ≤ (a : ℤ) *
      gramP (kq a b i) (kq a b (i + 1)) (kq a b (i + 2)) (kq a b (i + 3))
        (kq a b (i + 4)) := label_bound hba hi
  have hL := Lz_pos hba (by omega : i + 5 < P a b)
  have hq : 0 ≤ (qq a b i : ℤ) ^ 4 := by positivity
  nlinarith

/-- Actual orbit gaps in the large-scale range. -/
theorem orbit_middle_gaps_large (hba : b < a) {i : ℕ} (hi : i + 6 < P a b)
    {H X : ℤ} (hg : ∀ m < 5, kq a b (i + m) ≤ H)
    (hscale : (a : ℤ) * H ^ 5 * (24 * X + 464) < (qq a b i : ℤ) ^ 4) :
    2 * X < kq a b (i + 1) ∧ 2 * X < kq a b (i + 2) :=
  middle_gaps_large (by omega : (0 : ℤ) < a)
    (kq_pos (by omega)) (kq_pos (by omega)) (kq_pos (by omega))
    (kq_pos (by omega)) (kq_pos (by omega))
    (by simpa using hg 0 (by norm_num)) (hg 1 (by norm_num)) (hg 2 (by norm_num))
    (hg 3 (by norm_num)) (hg 4 (by norm_num)) (orbit_gram_lower hba hi) hscale

/-- Minor heights control the fourth obstruction's normalized coefficient. -/
lemma orbit_middle_coefficient_le (hba : b < a) {i : ℕ} (hi : i + 5 < P a b)
    {X : ℤ} (hX : 0 ≤ X) (hU : |U1z a b i| ≤ X) (hV : |U2z a b i| ≤ X) :
    ((U1z a b i : ℝ) / Lz a b i - (U2z a b i : ℝ) / Lz a b i) ≤ 2 * (X : ℝ) := by
  have hL : (1 : ℝ) ≤ Lz a b i := by exact_mod_cast Lz_pos hba hi
  have hU' : (U1z a b i : ℝ) ≤ (X : ℝ) := by exact_mod_cast (abs_le.mp hU).2
  have hV' : -(X : ℝ) ≤ (U2z a b i : ℝ) := by exact_mod_cast (abs_le.mp hV).1
  have hX' : (0 : ℝ) ≤ X := by exact_mod_cast hX
  rw [← sub_div, div_le_iff₀ (by linarith : (0 : ℝ) < Lz a b i)]
  nlinarith

/-- None of the four line obstruction equations can hold at a large-scale orbit window. -/
theorem orbit_line_obstructions_excluded (hba : b < a) {i : ℕ} (hi : i + 6 < P a b)
    {H X : ℤ} (hX : 1 ≤ X) (hg : ∀ m < 5, kq a b (i + m) ≤ H)
    (hU : |U1z a b i| ≤ X) (hV : |U2z a b i| ≤ X)
    (hscale : (a : ℤ) * H ^ 5 * (24 * X + 464) < (qq a b i : ℤ) ^ 4) :
    ¬ (pt a b i 3 = 0 ∨ pt a b i 2 - pt a b i 1 = 1 ∨
      pt a b i 3 - pt a b i 2 = 1 ∨
      pt a b i 4 - pt a b i 1 =
        (U1z a b i : ℝ) / Lz a b i - (U2z a b i : ℝ) / Lz a b i) := by
  obtain ⟨h1, h2⟩ := orbit_middle_gaps_large hba hi hg hscale
  have h3 := kq_pos (a := a) (b := b) (i := i + 3) (by omega)
  have h1' : 2 * (X : ℝ) < (kq a b (i + 1) : ℝ) := by exact_mod_cast h1
  have h2' : 2 * (X : ℝ) < (kq a b (i + 2) : ℝ) := by exact_mod_cast h2
  have h3' : (1 : ℝ) ≤ kq a b (i + 3) := by exact_mod_cast h3
  have hX' : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hp := pt_ge (a := a) (b := b) (i := i) (j := 3) (by omega)
  have hcoef := orbit_middle_coefficient_le hba (by omega) (by omega) hU hV
  apply line_obstructions_excluded (X := (X : ℝ)) (by norm_num at hp; linarith) _ _ hcoef
  all_goals simp only [pt, kq, Nat.add_assoc] at *
  all_goals push_cast at *
  all_goals linarith

end PierceLengthBound.FixedDividend
