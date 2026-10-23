/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveMonicHilbert
import Mathlib.Tactic

/-! Uniform finite unions of Hilbert exceptional sets and polynomial
coefficient cuts. The family cardinalities and degree bounds are fixed;
their coefficient height may grow polynomially with the original height. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

/-- Integers that are roots of some polynomial in a finite set `G` of nonzero
polynomials of degree at most `d` number at most `|G| d`. -/
theorem branch_rational_polynomial_cut_card_le (G : Finset ℚ[X]) (d : ℕ)
    (hG : ∀ q ∈ G, q ≠ 0 ∧ q.natDegree ≤ d)
    (S : Finset ℤ) (hS : ∀ t ∈ S, ∃ q ∈ G, q.eval (t : ℚ) = 0) :
    S.card ≤ G.card * d := by
  classical
  let T (q : ℚ[X]) := S.filter (fun t : ℤ => q.eval (t : ℚ) = 0)
  have hsubset : S ⊆ G.biUnion T := by
    intro t ht
    obtain ⟨q, hq, hz⟩ := hS t ht
    exact mem_biUnion.mpr ⟨q, hq, mem_filter.mpr ⟨ht, hz⟩⟩
  calc
    S.card ≤ ∑ q ∈ G, (T q).card := (card_le_card hsubset).trans card_biUnion_le
    _ ≤ ∑ _q ∈ G, d := by
      apply sum_le_sum
      intro q hq
      have hcard : ((T q).image (fun t : ℤ => (t : ℚ))).card = (T q).card :=
        Finset.card_image_of_injective _ Int.cast_injective
      rw [← hcard]
      apply (Polynomial.card_le_degree_of_subset_roots (p := q) ?_).trans (hG q hq).2
      intro t ht
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
      exact (Polynomial.mem_roots (hG q hq).1).mpr (mem_filter.mp hz).2
    _ = _ := by simp

/-- The one-parameter monic estimate for the union of the exceptional sets of
at most `N` monic irreducible families of total degree at most `d` and height
at most `K (H + 1)^E`. -/
theorem branch_finite_monic_hilbert_bound (d K E N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type*) [Field F]
      [Algebra ℤ[X] F] [IsFractionRing ℤ[X] F],
      ∀ (H B : ℕ) (G : Finset ℤ[X][X]), G.card ≤ N →
      (∀ p ∈ G, p.Monic ∧ Irreducible (p.map (algebraMap ℤ[X] F)) ∧
        CCDN.bivariateTotalDegree p ≤ d ∧
        ∀ i j, |(p.coeff i).coeff j| ≤ (K * (H + 1) ^ E : ℕ)) → 1 ≤ B →
      ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧ ∃ p ∈ G,
        ¬Irreducible ((p.map (evalRingHom t)).map (Int.castRingHom ℚ))) →
      (S.card : ℝ) ≤ C * (1 + Real.log (H + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := by
  classical
  obtain ⟨C₀, hC₀, hroot⟩ := branch_uniform_monic_hilbert_bound d
  let L₀ : ℝ := 1 + Real.log (K + 1 : ℕ) + E
  have hL : 0 < L₀ := by
    have hlog := Real.log_nonneg (by exact_mod_cast (show 1 ≤ K + 1 by omega) :
      (1 : ℝ) ≤ (K + 1 : ℕ))
    dsimp only [L₀]
    positivity
  refine ⟨(N + 1) * C₀ * L₀ ^ 4, by positivity, ?_⟩
  intro F _ _ _ H B G hcard hG hB S hS
  let T (p : ℤ[X][X]) := S.filter (fun t =>
    ¬Irreducible ((p.map (evalRingHom t)).map (Int.castRingHom ℚ)))
  have hsubset : S ⊆ G.biUnion T := by
    intro t ht
    obtain ⟨_htB, p, hp, hred⟩ := hS t ht
    exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨ht, hred⟩⟩
  have hsum : S.card ≤ ∑ p ∈ G, (T p).card :=
    (card_le_card hsubset).trans card_biUnion_le
  have hbound (p : ℤ[X][X]) (hp : p ∈ G) :
      ((T p).card : ℝ) ≤ C₀ * (1 + Real.log (K * (H + 1) ^ E + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := by
    obtain ⟨hpm, hpir, hpd, hph⟩ := hG p hp
    apply hroot F p hpm hpir hpd _ B hph hB (T p)
    intro t ht
    exact ⟨(hS t (mem_filter.mp ht).1).1, (mem_filter.mp ht).2⟩
  have hlog := branch_log_polynomial_height_le K E H
  have hlogH : 0 ≤ Real.log (H + 1 : ℕ) := Real.log_nonneg
    (by exact_mod_cast (show 1 ≤ H + 1 by omega))
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  have hcardR : (G.card : ℝ) ≤ N + 1 := by exact_mod_cast (show G.card ≤ N + 1 by omega)
  calc
    (S.card : ℝ) ≤ ∑ p ∈ G, ((T p).card : ℝ) := by exact_mod_cast hsum
    _ ≤ ∑ _p ∈ G, C₀ * (1 + Real.log (K * (H + 1) ^ E + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := sum_le_sum hbound
    _ = (G.card : ℝ) * (C₀ * (1 + Real.log (K * (H + 1) ^ E + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B)) := by simp
    _ ≤ (N + 1) * (C₀ * (L₀ * (1 + Real.log (H + 1 : ℕ))) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B)) := by gcongr
    _ = _ := by ring

/-- The same estimate after also adding the integer roots of at most `J` nonzero
cut polynomials of degree at most `D`. -/
theorem branch_finite_hilbert_with_cuts_bound (d K E N J D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type*) [Field F]
      [Algebra ℤ[X] F] [IsFractionRing ℤ[X] F],
      ∀ (H B : ℕ) (G : Finset ℤ[X][X]) (Q : Finset ℚ[X]),
      G.card ≤ N → Q.card ≤ J →
      (∀ p ∈ G, p.Monic ∧ Irreducible (p.map (algebraMap ℤ[X] F)) ∧
        CCDN.bivariateTotalDegree p ≤ d ∧
        ∀ i j, |(p.coeff i).coeff j| ≤ (K * (H + 1) ^ E : ℕ)) →
      (∀ q ∈ Q, q ≠ 0 ∧ q.natDegree ≤ D) → 1 ≤ B →
      ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧
        ((∃ p ∈ G, ¬Irreducible ((p.map (evalRingHom t)).map (Int.castRingHom ℚ))) ∨
          ∃ q ∈ Q, q.eval (t : ℚ) = 0)) →
      (S.card : ℝ) ≤ C * (1 + Real.log (H + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := by
  classical
  obtain ⟨C₀, hC₀, hcount⟩ := branch_finite_monic_hilbert_bound d K E N
  refine ⟨C₀ + J * D, by positivity, ?_⟩
  intro F _ _ _ H B G Q hGcard hQcard hG hQ hB S hS
  let P (t : ℤ) := ∃ p ∈ G,
    ¬Irreducible ((p.map (evalRingHom t)).map (Int.castRingHom ℚ))
  let S₁ := S.filter P
  let S₂ := S.filter (fun t => ¬P t)
  have h₁ := hcount F H B G hGcard hG hB S₁ (by
    intro t ht
    exact ⟨(hS t (mem_filter.mp ht).1).1, (mem_filter.mp ht).2⟩)
  have h₂ : S₂.card ≤ J * D := by
    apply (branch_rational_polynomial_cut_card_le Q D hQ S₂ ?_).trans
      (Nat.mul_le_mul_right D hQcard)
    intro t ht
    have h := mem_filter.mp ht
    exact (hS t h.1).2.resolve_left h.2
  have hsplit : S₁.card + S₂.card = S.card :=
    Finset.card_filter_add_card_filter_not P
  let W : ℝ := (1 + Real.log (H + 1 : ℕ)) ^ 4 *
    (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B)
  have hlogH : 0 ≤ Real.log (H + 1 : ℕ) := Real.log_nonneg
    (by exact_mod_cast (show 1 ≤ H + 1 by omega))
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  have hpowB : 1 ≤ (B : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hB) (by positivity)
  have hW : 1 ≤ W := by
    dsimp only [W]
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := by
        gcongr
        · exact one_le_pow₀ (by linarith)
        · linarith
  have h₂R : (S₂.card : ℝ) ≤ (J : ℝ) * D := by exact_mod_cast h₂
  have h₁' : (S₁.card : ℝ) ≤ C₀ * W := by simpa only [W, mul_assoc] using h₁
  have hadd : (J : ℝ) * D ≤ (J : ℝ) * D * W :=
    le_mul_of_one_le_right (by positivity) hW
  have htotal : (S.card : ℝ) ≤ (C₀ + J * D) * W := by
    rw [← hsplit, Nat.cast_add]
    calc
      _ ≤ C₀ * W + (J : ℝ) * D * W := add_le_add h₁' (h₂R.trans hadd)
      _ = _ := by ring
  simpa only [W, mul_assoc] using htotal

end
end PierceLengthBound.FixedDividend
