/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftDirection
public import PierceLengthBound.IntegralLiftConicProperness
public import PierceLengthBound.FixedDividendPolynomialSection
import all PierceLengthBound.FixedDividendTotalDegree

/-! The actual normalization equation gives a bounded polynomial cut on every
prime component, without requiring a conic parametrization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

private lemma mul_degree_bound {K σ : Type*} [CommRing K]
    {p q : MvPolynomial σ K} {u v : ℕ}
    (hp : p.totalDegree ≤ u) (hq : q.totalDegree ≤ v) :
    (p * q).totalDegree ≤ u + v := (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)

lemma clearedNewtonQuartic_totalDegree {K σ : Type*} [Field K]
    (c : Fin 4 → K) (z : Fin 3 → MvPolynomial σ K)
    (hz : ∀ j, (z j).totalDegree ≤ 1) (n q : MvPolynomial σ K)
    (hn : n.totalDegree ≤ 40) (hq : q.totalDegree ≤ 40) :
    (clearedNewtonQuartic (fun j => C (c j)) z n q).totalDegree ≤ 163 := by
  have hc (j) : (C (c j) : MvPolynomial σ K).totalDegree ≤ 0 := le_of_eq (totalDegree_C _)
  have hs (j) : (n + z j * q).totalDegree ≤ 41 :=
    (totalDegree_add _ _).trans (max_le (by omega) (mul_degree_bound (hz j) hq))
  have hp (j) : (q ^ j).totalDegree ≤ j * 40 :=
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hq)
  have h0 := mul_degree_bound (hc 0) (hp 4)
  have h1 := mul_degree_bound (mul_degree_bound (hc 1) hn) (hp 3)
  have h2 := mul_degree_bound (mul_degree_bound (mul_degree_bound (hc 2) hn) (hs 0)) (hp 2)
  have h3 := mul_degree_bound (mul_degree_bound (mul_degree_bound
    (mul_degree_bound (hc 3) hn) (hs 0)) (hs 1)) hq
  have h4 := mul_degree_bound (mul_degree_bound (mul_degree_bound hn (hs 0)) (hs 1)) (hs 2)
  unfold clearedNewtonQuartic
  apply (totalDegree_add _ _).trans
  apply max_le _ (h4.trans (by omega))
  apply (totalDegree_sub _ _).trans
  apply max_le _ (h3.trans (by omega))
  apply (totalDegree_add _ _).trans
  apply max_le _ (h2.trans (by omega))
  apply (totalDegree_sub _ _).trans
  exact max_le (h0.trans (by omega)) (h1.trans (by omega))

lemma muH4_totalDegree {K σ : Type*} [Field K]
    (k : Fin 5 → MvPolynomial σ K) (hk : ∀ j, (k j).totalDegree ≤ 1) :
    (muH4 (k 0) (k 1) (k 2) (k 3) (k 4)).totalDegree ≤ 6 := by
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  simp only [muH4, ← map_ofNat (C : K →+* MvPolynomial σ K)]
  -- Remove the simplifier annotation before the checked degree-proof tactic.
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let t ← Lean.Elab.Tactic.getMainTarget
    let g' ← g.replaceTargetDefEq t.consumeMData
    Lean.Elab.Tactic.replaceMainGoal [g']
  fixed_dividend_mv_degree

/-- Cleared equation A P(-q) = a H4 in the three original affine coordinates. -/
def jointNormalizationPolynomial (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  let n := orbitQuotientNumeratorQ a b i
  let q := orbitQuotientDenominatorQ a b i
  let k := jointGapPolynomials a b i
  C (Lz a b i : ℚ) * clearedNewtonQuartic
    (fun j : Fin 4 => C (coeffs (patternRhoQ a b i) (patternUQ a b i)
      (patternVQ a b i) j.castSucc)) X n q -
    C (a : ℚ) * muH4 (k 0) (k 1) (k 2) (k 3) (k 4) * q ^ 4

/-- Its degree is uniformly at most 166, independently of the pattern and dividend. -/
theorem jointNormalizationPolynomial_degree (a b i : ℕ) :
    (jointNormalizationPolynomial a b i).totalDegree ≤ 166 := by
  have h := orbitQuotient_polynomial_degrees a b i
  have hp := clearedNewtonQuartic_totalDegree
    (fun j : Fin 4 => coeffs (patternRhoQ a b i) (patternUQ a b i)
      (patternVQ a b i) j.castSucc) X (fun j => le_of_eq (totalDegree_X j)) _ _ h.1 h.2
  have hm := muH4_totalDegree _ (jointGapPolynomials_degree a b i)
  unfold jointNormalizationPolynomial
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (mul_degree_bound (le_of_eq (totalDegree_C _)) hp).trans (by omega)
  · exact (mul_degree_bound (mul_degree_bound (le_of_eq (totalDegree_C _)) hm)
      ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 4 h.2))).trans (by omega)

lemma jointNormalizationPolynomial_eval {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    eval (orbitFreeNodesQ a b i) (jointNormalizationPolynomial a b i) = 0 := by
  have hn := orbit_newton_normalization hba hi
  have hq := orbitQuotient_evaluation hba hi
  have hk := jointGapPolynomials_eval hba hi
  simp only [jointNormalizationPolynomial, clearedNewtonQuartic,
    map_sub, map_add, map_mul, map_pow, eval_C, eval_X]
  change (Lz a b i : ℚ) * clearedNewtonQuartic
    (fun j : Fin 4 => coeffs (patternRhoQ a b i) (patternUQ a b i)
      (patternVQ a b i) j.castSucc) (orbitFreeNodesQ a b i)
    (eval (orbitFreeNodesQ a b i) (orbitQuotientNumeratorQ a b i))
    (eval (orbitFreeNodesQ a b i) (orbitQuotientDenominatorQ a b i)) - _ = 0
  rw [clearedNewtonQuartic_div _ _ _ _ hq.1, ← hq.2, ← mul_assoc, hn]
  rw [map_muH4]
  simp [hk]

lemma jointNormalizationPolynomial_congr {a b i l : ℕ} (h : theta a b i = theta a b l) :
    jointNormalizationPolynomial a b i = jointNormalizationPolynomial a b l := by
  obtain ⟨h0, hρ, hu, hv, hρ', hu', hv'⟩ := orbit_pattern_eq_of_theta h
  simp only [jointNormalizationPolynomial, orbitQuotientNumeratorQ, orbitQuotientDenominatorQ,
    orbitCurveCofactorsQ, jointGapPolynomials, h0, hρ, hu, hv, hρ', hu', hv']

/-- If normalization is not an identity on a prime degree-d component, it has
at most 166d distinct actual points of the fixed pattern. -/
theorem jointNormalizationPolynomial_proper_cut {a b i d : ℕ} (hba : b < a)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    (hproper : jointNormalizationPolynomial a b i ∉ I)
    {ι : Type*} [Fintype ι] (l : ι → ℕ)
    (hinj : Function.Injective (fun j => orbitFreeNodesQ a b (l j)))
    (hi : ∀ j, l j + 7 < P a b) (hθ : ∀ j, theta a b i = theta a b (l j))
    (hp : ∀ j, orbitFreeNodesQ a b (l j) ∈ coordinateZeroLocus I) :
    Fintype.card ι ≤ 166 * d := by
  classical
  apply polynomial_section_card_le_degree I d hd _ hproper 166
    (jointNormalizationPolynomial_degree a b i) _ hinj hp
  intro j
  rw [jointNormalizationPolynomial_congr (hθ j)]
  exact jointNormalizationPolynomial_eval hba (hi j)

/-- Quotient reconstruction makes the three free nodes injective on supported
states of one complete pattern. -/
theorem orbitFreeNodesQ_injective_of_pattern {a b i : ℕ} (hba : b < a)
    {ι : Type*} (l : ι → ℕ) (hl : Function.Injective l)
    (hi : ∀ j, l j + 7 < P a b) (hθ : ∀ j, theta a b i = theta a b (l j)) :
    Function.Injective (fun j => orbitFreeNodesQ a b (l j)) := by
  intro j k he
  dsimp only at he
  have hn := orbitQuotient_polynomials_congr ((hθ j).symm.trans (hθ k))
  have hqj := (orbitQuotient_evaluation hba (hi j)).2
  have hqk := (orbitQuotient_evaluation hba (hi k)).2
  have hq : qq a b (l j) = qq a b (l k) := by
    have heq : (qq a b (l j) : ℚ) = (qq a b (l k) : ℚ) := by
      rw [hqj, hqk, hn.1, hn.2, he]
    exact_mod_cast heq
  apply hl
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (qq_strictMono (a := a) (b := b) hlt (by have := hi k; omega)).ne hq
  · exact (qq_strictMono (a := a) (b := b) hlt (by have := hi j; omega)).ne hq.symm

/-- In a family of distinct supported states, normalization either holds on the
whole prime component or the family contains at most 166d states. -/
theorem jointNormalizationPolynomial_identity_or_card_bound {a b i d : ℕ} (hba : b < a)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    {ι : Type*} [Fintype ι] (l : ι → ℕ) (hl : Function.Injective l)
    (hi : ∀ j, l j + 7 < P a b) (hθ : ∀ j, theta a b i = theta a b (l j))
    (hp : ∀ j, orbitFreeNodesQ a b (l j) ∈ coordinateZeroLocus I) :
    jointNormalizationPolynomial a b i ∈ I ∨ Fintype.card ι ≤ 166 * d := by
  classical
  by_cases h : jointNormalizationPolynomial a b i ∈ I
  · exact Or.inl h
  · exact Or.inr (jointNormalizationPolynomial_proper_cut hba I hd h l
      (orbitFreeNodesQ_injective_of_pattern hba l hl hi hθ) hi hθ hp)

end
end PierceLengthBound.FixedDividend
