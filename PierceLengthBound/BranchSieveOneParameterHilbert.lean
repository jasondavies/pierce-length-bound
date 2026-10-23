/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveUniformEquationFamily
public import PierceLengthBound.BranchSieveNestedRootBound
import Mathlib.Tactic

/-! A coefficient-uniform one-parameter Hilbert irreducibility estimate.
The proof constructs integral coefficient resolvents and counts their
integer roots using the proved affine plane-curve estimate. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

theorem branch_log_polynomial_height_le (C E H : ℕ) :
    1 + Real.log (C * (H + 1) ^ E + 1 : ℕ) ≤
      (1 + Real.log (C + 1 : ℕ) + E) * (1 + Real.log (H + 1 : ℕ)) := by
  have hpow : 1 ≤ (H + 1) ^ E := Nat.one_le_pow _ _ (by omega)
  have hb : C * (H + 1) ^ E + 1 ≤ (C + 1) * (H + 1) ^ E := by nlinarith
  have hlog : Real.log (C * (H + 1) ^ E + 1 : ℕ) ≤
      Real.log (C + 1 : ℕ) + E * Real.log (H + 1 : ℕ) := by
    calc
      _ ≤ Real.log ((C + 1 : ℕ) * ((H + 1 : ℕ) : ℝ) ^ E) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hb)
      _ = _ := by rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hc : 0 ≤ Real.log (C + 1 : ℕ) := Real.log_nonneg
    (by exact_mod_cast (show 1 ≤ C + 1 by omega))
  have hh : 0 ≤ Real.log (H + 1 : ℕ) := Real.log_nonneg
    (by exact_mod_cast (show 1 ≤ H + 1 by omega))
  have he : (0 : ℝ) ≤ E := by positivity
  nlinarith

theorem branch_one_parameter_proper_factor_bound (n D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F L : Type*) [Field F]
      [Algebra ℤ[X] F] [IsFractionRing ℤ[X] F] [Field L]
      [Algebra ℤ[X] L] [Algebra F L] [IsScalarTower ℤ[X] F L]
      [FaithfulSMul ℤ[X] L],
      ∀ (p : ℤ[X][X]), p.Monic → p.natDegree = n →
      Irreducible (p.map (algebraMap ℤ[X] F)) →
      (p.map (algebraMap ℤ[X] L)).Splits →
      ∀ H B : ℕ, (∀ j, (p.coeff j).natDegree ≤ D) →
      (∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ)) → 1 ≤ B →
      ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧ ∃ q : ℤ[X], q.Monic ∧
        q ∣ p.map (evalRingHom t) ∧ 0 < q.natDegree ∧ q.natDegree < n) →
      (S.card : ℝ) ≤ C * (1 + Real.log (H + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := by
  classical
  obtain ⟨M, E, K, hK, hfamily⟩ := branch_uniform_integer_equation_family n D
  obtain ⟨C₀, hC₀, hroot⟩ := branch_uniform_nested_root_bound M
  let L₀ : ℝ := 1 + Real.log (K + 1 : ℕ) + E
  have hL : 0 < L₀ := by
    have hlog := Real.log_nonneg (by exact_mod_cast (show 1 ≤ K + 1 by omega) :
      (1 : ℝ) ≤ (K + 1 : ℕ))
    dsimp only [L₀]
    positivity
  refine ⟨(2 ^ n * (n + 1) : ℕ) * C₀ * L₀ ^ 4, by positivity, ?_⟩
  intro F L _ _ _ _ _ _ _ _ p hp hn hir hsplit H B hD hH hB S hS
  obtain ⟨G, hcard, hG, hcover⟩ := hfamily F L p hp hn hir hsplit H hD hH
  let T (f : ℤ[X][X]) := S.filter (fun t => ∃ y : ℤ, (f.map (evalRingHom t)).eval y = 0)
  have hsubset : S ⊆ G.biUnion T := by
    intro t ht
    obtain ⟨_htB, q, hq, hqdiv, hqpos, hqlt⟩ := hS t ht
    obtain ⟨f, hf, y, hy⟩ := hcover t q hq hqdiv hqpos hqlt
    exact mem_biUnion.mpr ⟨f, hf, mem_filter.mpr ⟨ht, y, hy⟩⟩
  have hsum : S.card ≤ ∑ f ∈ G, (T f).card :=
    (card_le_card hsubset).trans (card_biUnion_le)
  have hbound (f : ℤ[X][X]) (hf : f ∈ G) :
      ((T f).card : ℝ) ≤ C₀ * (1 + Real.log (K * (H + 1) ^ E + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := by
    obtain ⟨hfm, hfir, hfdeg, hfd, hfh⟩ := hG f hf
    apply hroot F f hfm hfir hfd hfdeg _ B hfh hB (T f)
    intro t ht
    have hh := mem_filter.mp ht
    exact ⟨(hS t hh.1).1, hh.2⟩
  have hlog := branch_log_polynomial_height_le K E H
  have hlogH : 0 ≤ Real.log (H + 1 : ℕ) := Real.log_nonneg
    (by exact_mod_cast (show 1 ≤ H + 1 by omega))
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  calc
    (S.card : ℝ) ≤ ∑ f ∈ G, ((T f).card : ℝ) := by exact_mod_cast hsum
    _ ≤ ∑ _f ∈ G, C₀ * (1 + Real.log (K * (H + 1) ^ E + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := sum_le_sum hbound
    _ = (G.card : ℝ) * (C₀ * (1 + Real.log (K * (H + 1) ^ E + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B)) := by simp
    _ ≤ (2 ^ n * (n + 1) : ℕ) * (C₀ * (L₀ * (1 + Real.log (H + 1 : ℕ))) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B)) := by
      gcongr
    _ = _ := by ring

end
end PierceLengthBound.FixedDividend
