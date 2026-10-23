/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionWindow
public import PierceLengthBound.LatticeCurvature

/-! From the six-term polar estimate to integer-power counting branches.
The estimate is defined here and supplied by the arithmetic and geometric proofs
assembled in `PolarProjectionMain`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The five good-pattern terms for an arbitrary powered-graph degree. -/
def polarGoodTerms (H X S Y h m n : ℕ) : ℝ :=
  (X : ℝ) ^ 5 + (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) +
    (X : ℝ) ^ (5 - (1 / (h : ℝ)) / 3) * (H : ℝ) ^ (1 / (h : ℝ)) +
    (X : ℝ) ^ (5 - (2 * m / (h : ℝ)) / 3) * (S : ℝ) ^ (m / (h : ℝ)) +
    (X : ℝ) ^ 5 * (Y : ℝ) ^ (n / (h : ℝ))

/-- The contribution of the enlarged bad-pattern class. -/
def polarBadTerm (H X S Y : ℕ) : ℝ :=
  (X : ℝ) ^ (14 / 3 : ℝ) * ((max H (max S Y) : ℕ) : ℝ) ^ (1 / 17 : ℝ)

lemma latticeCountBranches_mono {K K' T H X S Y h m n : ℕ} (hK : K ≤ K')
    (hc : LatticeJointCountBranches K T H X S Y h m n) :
    LatticeJointCountBranches K' T H X S Y h m n := by
  rcases hc with c | c | c | c | c
  · exact Or.inl (c.trans (by gcongr))
  · exact Or.inr (Or.inl (c.trans (by gcongr)))
  · exact Or.inr (Or.inr (Or.inl (c.trans (by gcongr))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (c.trans (by gcongr)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (c.trans (by gcongr)))))

/-- A single integral coefficient for all good- and bad-pattern branches. -/
def polarProjectionCountSlack (R m n : ℕ) : ℕ :=
  (10 * (R + 1)) ^ (3 * polarProjectionGraphDegree m n + 51)

/-- The displayed six-term estimate entails precisely the required counting branches. -/
theorem polar_projection_branches_of_six_term_count {T H X S Y R m n : ℕ} (hm : 0 < m)
    (hcount : (T : ℝ) ≤ R *
      (polarGoodTerms H X S Y (polarProjectionGraphDegree m n) m n + polarBadTerm H X S Y)) :
    PolarProjectionCountBranches (polarProjectionCountSlack R m n) T H X S Y m n := by
  let h := polarProjectionGraphDegree m n
  let D := 10 * (R + 1)
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hpow {b k : ℕ} (hb : b ≤ D) (hk : k ≤ 3 * h + 51) :
      b ^ k ≤ polarProjectionCountSlack R m n :=
    (Nat.pow_le_pow_left hb k).trans (Nat.pow_le_pow_right hD hk)
  have htwo : (T : ℝ) ≤ (2 * R : ℕ) * polarGoodTerms H X S Y h m n ∨
      (T : ℝ) ≤ (2 * R : ℕ) * polarBadTerm H X S Y := by
    by_contra hn
    push Not at hn
    push_cast at hn
    dsimp [h] at hn
    nlinarith
  rcases htwo with hg | hb
  · left
    apply latticeCountBranches_mono
      (hpow (b := 5 * (2 * R + 1)) (k := 3 * h) (by dsimp [D]; omega) (by omega))
    exact lattice_branches_of_five_term_count hm
      (by dsimp [h, polarProjectionGraphDegree]; omega) hg
  · right
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg T) hb 51
    have hx : ((X : ℝ) ^ (14 / 3 : ℝ)) ^ 51 = (X : ℝ) ^ 238 :=
      rpow_pow_natCast (Nat.cast_nonneg _) 51 (by norm_num)
    have hy : (((max H (max S Y) : ℕ) : ℝ) ^ (1 / 17 : ℝ)) ^ 51 =
        ((max H (max S Y) : ℕ) : ℝ) ^ 3 :=
      rpow_pow_natCast (Nat.cast_nonneg _) 51 (by norm_num)
    dsimp [polarBadTerm] at hp
    rw [mul_pow, mul_pow, hx, hy] at hp
    have hc : T ^ 51 ≤ (2 * R) ^ 51 * X ^ 238 * (max H (max S Y)) ^ 3 := by
      exact_mod_cast (by simpa only [mul_assoc] using hp :
        (T : ℝ) ^ 51 ≤ (2 * R : ℕ) ^ 51 * (X : ℝ) ^ 238 *
          ((max H (max S Y) : ℕ) : ℝ) ^ 3)
    have hk : (2 * R) ^ 51 ≤ polarProjectionCountSlack R m n :=
      hpow (by dsimp [D]; omega) (by omega)
    have hc' : T ^ 51 ≤ polarProjectionCountSlack R m n * X ^ 238 *
        (max H (max S Y)) ^ 3 := hc.trans (by gcongr)
    rcases le_total H (max S Y) with hH | hH
    · rw [max_eq_right hH] at hc'
      rcases le_total S Y with hS | hS
      · exact Or.inr (Or.inr (by simpa only [max_eq_right hS] using hc'))
      · exact Or.inr (Or.inl (by simpa only [max_eq_left hS] using hc'))
    · exact Or.inl (by simpa only [max_eq_left hH] using hc')

/-- The local six-term estimate required by the polar-projection proposal, on actual windows.
This is a named proposition, not a claim that the estimate has been established. -/
def PolarProjectionSixTermEstimate (m n : ℕ) (R : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    (T : ℝ) ≤ R a *
      (polarGoodTerms (selectedGapHeight a A T) (selectedMinorHeight a A T)
        (selectedAllMinorHeight a A T) (selectedRankFiveHeight a A T)
        (polarProjectionGraphDegree m n) m n +
      polarBadTerm (selectedGapHeight a A T) (selectedMinorHeight a A T)
        (selectedAllMinorHeight a A T) (selectedRankFiveHeight a A T))

end
end PierceLengthBound.FixedDividend
