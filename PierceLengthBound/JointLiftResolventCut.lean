/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import all PierceLengthBound.FixedDividendTotalDegree
public import PierceLengthBound.JointLiftNormalizationCut

/-! # The resolvent cut

The resolvent identity `E₀ P₄(-Q) = a ((Q - p₃) H₃ - H₀₁₃)`, with denominators cleared, is a
polynomial of total degree at most `404` in the free nodes that vanishes at the free nodes of
every state with the given pattern. On a prime component of degree `d` it either lies in the
component's ideal or at most `404 d` states of the pattern have free nodes on the component
(Lemma 8.3). -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- The cubic coefficient `p₃ = ū₂ - 1 - s₁ - s₂ - s₃` of the monic Newton quartic `P₄`. -/
def jointQuarticCubicCoefficient (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  C (patternVQ a b i - 1) - X 0 - X 1 - X 2

lemma jointQuarticCubicCoefficient_degree (a b i : ℕ) :
    (jointQuarticCubicCoefficient a b i).totalDegree ≤ 1 := by
  unfold jointQuarticCubicCoefficient
  apply (totalDegree_sub _ _).trans
  apply max_le _ (le_of_eq (totalDegree_X _))
  apply (totalDegree_sub _ _).trans
  apply max_le _ (le_of_eq (totalDegree_X _))
  exact (totalDegree_sub _ _).trans
    (max_le (by rw [totalDegree_C]; omega) (le_of_eq (totalDegree_X _)))

lemma jointQuarticCubicCoefficient_eval (a b i : ℕ) :
    eval (orbitFreeNodesQ a b i) (jointQuarticCubicCoefficient a b i) =
      (orbitNewtonQuarticQ a b i).coeff 3 := by
  simp [jointQuarticCubicCoefficient, orbitNewtonQuarticQ, firstNewtonQuartic_eq,
    monicQuartic_coeff, firstNewtonCoeffs, coeffs]
  ring

lemma rawHankelMixed_totalDegree (k : Fin 5 → MvPolynomial (Fin 3) ℚ)
    (hk : ∀ j, (k j).totalDegree ≤ 1) :
    (rawHankelMixed (k 0) (k 1) (k 2) (k 3)).totalDegree ≤ 4 := by
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  have h3 := hk 3
  unfold rawHankelMixed
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let t ← Lean.Elab.Tactic.getMainTarget
    let g' ← g.replaceTargetDefEq t.consumeMData
    Lean.Elab.Tactic.replaceMainGoal [g']
  fixed_dividend_mv_degree

/-- The resolvent identity `E₀ P₄(-Q) = a ((Q - p₃) H₃ - H₀₁₃)` with the denominators of `Q`
and `E₀` cleared, as a polynomial in the three free nodes. -/
def jointResolventPolynomial (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  let n := orbitQuotientNumeratorQ a b i
  let q := orbitQuotientDenominatorQ a b i
  let k := jointGapPolynomials a b i
  orbitLiftNumeratorQ a b i * clearedNewtonQuartic
    (fun j : Fin 4 => C (coeffs (patternRhoQ a b i) (patternUQ a b i)
      (patternVQ a b i) j.castSucc)) X n q -
    C (a : ℚ) * ((n - jointQuarticCubicCoefficient a b i * q) *
      rawHankelThree (k 0) (k 1) (k 2) - rawHankelMixed (k 0) (k 1) (k 2) (k 3) * q) *
      q ^ 3 * orbitLiftDenominatorQ a b i

/-- The cleared resolvent polynomial has total degree at most `404`. -/
theorem jointResolventPolynomial_degree (a b i : ℕ) :
    (jointResolventPolynomial a b i).totalDegree ≤ 404 := by
  have hq := orbitQuotient_polynomial_degrees a b i
  have hE := orbitLift_polynomial_degrees a b i
  have hp := clearedNewtonQuartic_totalDegree
    (fun j : Fin 4 => coeffs (patternRhoQ a b i) (patternUQ a b i)
      (patternVQ a b i) j.castSucc) X (fun j => le_of_eq (totalDegree_X j)) _ _ hq.1 hq.2
  have hc := jointQuarticCubicCoefficient_degree a b i
  have hk := jointGapPolynomials_degree a b i
  have hB := rawHankelThree_degree (hk 0) (hk 1) (hk 2)
  have hM := rawHankelMixed_totalDegree _ hk
  have ht : ((orbitQuotientNumeratorQ a b i - jointQuarticCubicCoefficient a b i *
      orbitQuotientDenominatorQ a b i) * rawHankelThree (jointGapPolynomials a b i 0)
        (jointGapPolynomials a b i 1) (jointGapPolynomials a b i 2) -
      rawHankelMixed (jointGapPolynomials a b i 0) (jointGapPolynomials a b i 1)
        (jointGapPolynomials a b i 2) (jointGapPolynomials a b i 3) *
        orbitQuotientDenominatorQ a b i).totalDegree ≤ 44 := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_mul _ _).trans
      have hsub := totalDegree_sub (orbitQuotientNumeratorQ a b i)
        (jointQuarticCubicCoefficient a b i * orbitQuotientDenominatorQ a b i)
      have hmul := totalDegree_mul (jointQuarticCubicCoefficient a b i)
        (orbitQuotientDenominatorQ a b i)
      omega
    · exact (totalDegree_mul _ _).trans (by omega)
  unfold jointResolventPolynomial
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans (by omega)
  · have mulb {p q : MvPolynomial (Fin 3) ℚ} {u v : ℕ}
        (hu : p.totalDegree ≤ u) (hv : q.totalDegree ≤ v) :
        (p * q).totalDegree ≤ u + v :=
      (totalDegree_mul _ _).trans (Nat.add_le_add hu hv)
    exact (mulb (mulb (mulb (le_of_eq (totalDegree_C _)) ht)
      ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 3 hq.2))) hE.2).trans (by omega)


/-- The cleared resolvent polynomial vanishes at the free nodes of state `i`. -/
theorem jointResolventPolynomial_eval {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    eval (orbitFreeNodesQ a b i) (jointResolventPolynomial a b i) = 0 := by
  let ev := eval (orbitFreeNodesQ a b i)
  let n := ev (orbitQuotientNumeratorQ a b i)
  let q := ev (orbitQuotientDenominatorQ a b i)
  have hq := orbitQuotient_evaluation hba hi
  have hI := orbitLift_evaluation hba hi
  have hr := orbit_integralLift_raw_resolvent_Q hba hi
  have hn : ev (orbitLiftNumeratorQ a b i) =
      (integralLiftCoordinate a b i : ℚ) * ev (orbitLiftDenominatorQ a b i) :=
    ((eq_div_iff hI.1).mp hI.2).symm
  have hnq : n = (qq a b i : ℚ) * q := ((eq_div_iff hq.1).mp hq.2).symm
  have heval : ev (clearedNewtonQuartic
      (fun j : Fin 4 => C (coeffs (patternRhoQ a b i) (patternUQ a b i)
        (patternVQ a b i) j.castSucc)) X
      (orbitQuotientNumeratorQ a b i) (orbitQuotientDenominatorQ a b i)) =
      (orbitNewtonQuarticQ a b i).eval (-(qq a b i : ℚ)) * q ^ 4 := by
    simp only [clearedNewtonQuartic, map_add, map_sub, map_mul, map_pow, eval_C, eval_X, ev]
    change clearedNewtonQuartic
      (fun j : Fin 4 => coeffs (patternRhoQ a b i) (patternUQ a b i)
        (patternVQ a b i) j.castSucc) (orbitFreeNodesQ a b i) n q = _
    rw [clearedNewtonQuartic_div _ _ _ _ hq.1, ← hq.2]
    rfl
  have hk := jointGapPolynomials_eval hba hi
  have hB : ev (rawHankelThree (jointGapPolynomials a b i 0)
      (jointGapPolynomials a b i 1) (jointGapPolynomials a b i 2)) =
      rawHankelThree (kq a b i : ℚ) (kq a b (i + 1) : ℚ) (kq a b (i + 2) : ℚ) := by
    simp [ev, rawHankelThree, hk]
  have hM : ev (rawHankelMixed (jointGapPolynomials a b i 0)
      (jointGapPolynomials a b i 1) (jointGapPolynomials a b i 2)
      (jointGapPolynomials a b i 3)) =
      rawHankelMixed (kq a b i : ℚ) (kq a b (i + 1) : ℚ)
        (kq a b (i + 2) : ℚ) (kq a b (i + 3) : ℚ) := by
    simp [ev, rawHankelMixed, hk]
  have hca : ev (C (a : ℚ)) = (a : ℚ) := by simp [ev]
  change ev (jointResolventPolynomial a b i) = 0
  simp only [jointResolventPolynomial, map_sub, map_mul, map_pow, hca,
    heval, hn, hB, hM]
  change (integralLiftCoordinate a b i : ℚ) * ev (orbitLiftDenominatorQ a b i) *
      ((orbitNewtonQuarticQ a b i).eval (-(qq a b i : ℚ)) * q ^ 4) -
    (a : ℚ) * ((n - ev (jointQuarticCubicCoefficient a b i) * q) *
      rawHankelThree (kq a b i : ℚ) (kq a b (i + 1) : ℚ) (kq a b (i + 2) : ℚ) -
      rawHankelMixed (kq a b i : ℚ) (kq a b (i + 1) : ℚ)
        (kq a b (i + 2) : ℚ) (kq a b (i + 3) : ℚ) * q) * q ^ 3 *
      ev (orbitLiftDenominatorQ a b i) = 0
  rw [hnq, show ev (jointQuarticCubicCoefficient a b i) =
    (orbitNewtonQuarticQ a b i).coeff 3 from jointQuarticCubicCoefficient_eval a b i]
  linear_combination (ev (orbitLiftDenominatorQ a b i) * q ^ 4) * hr

lemma jointResolventPolynomial_congr {a b i l : ℕ} (h : theta a b i = theta a b l) :
    jointResolventPolynomial a b i = jointResolventPolynomial a b l := by
  obtain ⟨_, hρ, hu, hv, hρ', hu', hv'⟩ := orbit_pattern_eq_of_theta h
  simp only [jointResolventPolynomial, jointQuarticCubicCoefficient,
    orbitQuotientNumeratorQ, orbitQuotientDenominatorQ, orbitLiftNumeratorQ,
    orbitLiftDenominatorQ, orbitCurveCofactorsQ, jointGapPolynomials,
    hρ, hu, hv, hρ', hu', hv']

/-- For a family of distinct states with the pattern of `i` whose free nodes lie on the prime
component `I` of degree `d`, either the cleared resolvent polynomial lies in `I` or the family
has at most `404 d` members. -/
theorem jointResolventPolynomial_identity_or_card_bound {a b i d : ℕ} (hba : b < a)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    {ι : Type*} [Fintype ι] (l : ι → ℕ) (hl : Function.Injective l)
    (hi : ∀ j, l j + 7 < P a b) (hθ : ∀ j, theta a b i = theta a b (l j))
    (hp : ∀ j, orbitFreeNodesQ a b (l j) ∈ coordinateZeroLocus I) :
    jointResolventPolynomial a b i ∈ I ∨ Fintype.card ι ≤ 404 * d := by
  classical
  by_cases h : jointResolventPolynomial a b i ∈ I
  · exact Or.inl h
  · right
    apply polynomial_section_card_le_degree I d hd _ h 404
      (jointResolventPolynomial_degree a b i) _
      (orbitFreeNodesQ_injective_of_pattern hba l hl hi hθ) hp
    intro j
    rw [jointResolventPolynomial_congr (hθ j)]
    exact jointResolventPolynomial_eval hba (hi j)

end
end PierceLengthBound.FixedDividend
