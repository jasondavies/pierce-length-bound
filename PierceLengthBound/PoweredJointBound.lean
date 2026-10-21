/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PoweredJointWindow
public import PierceLengthBound.JointLiftOptimization

/-! Unconditional optimized length bounds from fixed positive integer powers
of the two joint invariants. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The larger of the two powered window exponents. -/
def poweredJointExponent (m n : ℕ) : ℝ :=
  let L := 10 * n + 7 * m
  max (((15 * L + m : ℕ) : ℝ) / (51 * L + 3 * m : ℕ))
    (((15 * L + 6 * n : ℕ) : ℝ) / (51 * L + 20 * n : ℕ))

lemma poweredJointExponent_ge_base {m n : ℕ} (hm : 0 < m) :
    (5 : ℝ) / 17 ≤ poweredJointExponent m n := by
  apply le_trans _ (le_max_left _ _)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  push_cast
  apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
  nlinarith

/-- Every fixed pair of positive powers gives its asserted unconditional
length exponent; all local geometry and curve counting are proved inputs. -/
theorem P_le_powered_joint (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (poweredJointExponent m n + ε) := by
  obtain ⟨R, hR, hcount⟩ := poweredJointThreeTermEstimate_exists m n hm hn
  let L := 10 * n + 7 * m
  let K := fun a => (3 * (R a + 1)) ^ L
  let C₀ := poweredJointWindowBase m n L
  let q := 17 + 10 * L + 5 * n + m
  let S := fun a => C₀ * (K a + 1) * tauMax (32 * a ^ 7) ^ q
  have hK : SlowGrowth K := ((slowGrowth_const 3).mul (slowGrowth_add_one hR)).pow L
  have hS : SlowGrowth S := ((slowGrowth_const C₀).mul (slowGrowth_add_one hK)).mul
    ((tauMax_slow 32 7).pow q)
  have hα := poweredJointExponent_ge_base (n := n) hm
  apply P_le_of_real_visits hS (by linarith : 0 ≤ poweredJointExponent m n)
  intro a b k _hb hba
  by_cases hT : (visits a b k).card ≤ 35
  · exact Or.inl hT
  right
  set T := (visits a b k).card
  have hne : (visits a b k).Nonempty := by rw [← Finset.card_pos]; omega
  have W := visits_window hba.le hne
  set s := (visits a b k).min' hne
  have hmem : ∀ j < T, 2 ^ k ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * 2 ^ k := W.mem
  have hsT : s + T ≤ P a b := by
    have h := (hmem (T - 1) (by omega)).1
    have := lt_P_of_orb_pos (a := a) (b := b) (i := s + (T - 1))
      (lt_of_lt_of_le (Nat.two_pow_pos k) h)
    omega
  apply window_real_of_powered_joint_count (K := K a) hm (by omega) hα
    (le_max_left _ _) (le_max_right _ _) (by omega)
    (six_step_bound W (by omega)) (drop_bound W (tauMax_divBound a) (by omega))
  dsimp only
  intro hscale
  apply powered_joint_branches_of_three_term_count (L := L) (R := R a) (by dsimp [L]; omega)
  simpa only [PoweredJointThreeTermEstimate, selectedGapHeight, selectedMinorHeight,
    selectedCurvatureHeight, selectedRankFiveHeight, L, Nat.cast_max, Nat.cast_pow] using
    hcount a b s T (2 ^ k) hba hmem hsT (by omega) hscale

/-- The explicit rational choice m=50, n=51. -/
theorem P_le_2201_7480 :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((2201 : ℝ) / 7480 + ε) := by
  simpa only [poweredJointExponent, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat,
    show max ((12950 : ℝ) / 44010) ((13206 : ℝ) / 44880) = 2201 / 7480 by norm_num] using
    P_le_powered_joint 50 51 (by decide) (by decide)

/-- Optimizing fixed integer powers gives the algebraic exponent of the candidate. -/
theorem P_le_joint_optimal :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (jointOptimalExponent + ε) := by
  intro ε hε
  obtain ⟨m, n, hm, hn, happ⟩ := jointOptimal_integer_powers (by positivity : 0 < ε / 2)
  have he : poweredJointExponent m n < jointOptimalExponent + ε / 2 := by
    simpa only [poweredJointExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using happ
  obtain ⟨C, hC, hbound⟩ := P_le_powered_joint m n hm hn (ε / 2) (by positivity)
  refine ⟨C, hC, fun a b hb hba => ?_⟩
  apply (hbound a b hb hba).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ a by omega))
  linarith

end
end PierceLengthBound.FixedDividend
