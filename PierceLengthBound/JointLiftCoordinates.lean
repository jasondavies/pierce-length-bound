/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftCoordinateSystem
import all PierceLengthBound.FixedDividendTotalDegree
public import PierceLengthBound.JointLiftAlgebra
public import PierceLengthBound.IntegralLiftQuotientNormalization

/-! # Polynomial coordinates of the joint lift

The joint coordinates `W₀, W₁, W₂, J` of Section 8.6 as quotients of polynomials in the three
free nodes over one common denominator `Q · H₃ · k₁`, with total-degree bounds for numerators
and denominator, and their values at the free nodes of an orbit state: the curvature-minor
vector `W` and the rank-five coordinate `J = N₀ Ψ`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Matrix

/-- The five gaps `k₀, …, k₄` of the pattern at state `i`, as linear polynomials in the three
free nodes. -/
def jointGapPolynomials (a b i : ℕ) : Fin 5 → MvPolynomial (Fin 3) ℚ :=
  lineGaps (C (patternRhoQ a b i)) (C (patternUQ a b i)) (C (patternVQ a b i))
    (C (patternRhoQ a b (i + 1))) (C (patternUQ a b (i + 1)))
    (C (patternVQ a b (i + 1))) (X 0) (X 1) (X 2)

lemma jointGapPolynomials_eval {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (j : Fin 5) :
    eval (orbitFreeNodesQ a b i) (jointGapPolynomials a b i j) = (kq a b (i + j.val) : ℚ) := by
  unfold jointGapPolynomials
  rw [map_lineGaps]
  simp only [eval_C, eval_X]
  exact orbit_rational_lineGaps hba (by omega) j

lemma jointGapPolynomials_degree (a b i : ℕ) (j : Fin 5) :
    (jointGapPolynomials a b i j).totalDegree ≤ 1 := by
  have h0 : (X 0 : MvPolynomial (Fin 3) ℚ).totalDegree ≤ 1 := le_of_eq (totalDegree_X _)
  have h1 : (X 1 : MvPolynomial (Fin 3) ℚ).totalDegree ≤ 1 := le_of_eq (totalDegree_X _)
  have h2 : (X 2 : MvPolynomial (Fin 3) ℚ).totalDegree ≤ 1 := le_of_eq (totalDegree_X _)
  generalize hx0 : (X 0 : MvPolynomial (Fin 3) ℚ) = x0 at *
  generalize hx1 : (X 1 : MvPolynomial (Fin 3) ℚ) = x1 at *
  generalize hx2 : (X 2 : MvPolynomial (Fin 3) ℚ) = x2 at *
  fin_cases j <;> simp only [jointGapPolynomials, lineGaps, Fin.isValue, hx0, hx1, hx2, fourthNode,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val_zero, cons_val_one, cons_val, ge_iff_le]
  all_goals fixed_dividend_mv_degree

/-- The rank-five coordinate `J = N₀ Ψ`, a cubic polynomial in the three free nodes. -/
def jointRankFivePolynomial (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  C (Lz a b i : ℚ) * curveNorm (patternRhoQ a b i) (patternUQ a b i) (patternVQ a b i)
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))

lemma jointRankFivePolynomial_degree (a b i : ℕ) :
    (jointRankFivePolynomial a b i).totalDegree ≤ 3 := by
  unfold jointRankFivePolynomial
  have h := curveNorm_degree_le_three (patternRhoQ a b i) (patternUQ a b i) (patternVQ a b i)
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
  exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using h)

lemma jointRankFivePolynomial_eval_cast {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    (eval (orbitFreeNodesQ a b i) (jointRankFivePolynomial a b i) : ℝ) =
      (Lz a b i : ℝ) * orbitNorm a b i := by
  unfold jointRankFivePolynomial
  rw [map_mul, eval_C, eval_curveNorm]
  change (algebraMap ℚ ℝ) (_ * _) = _
  rw [map_mul, map_lineNorm]
  change (Lz a b i : ℝ) * lineNorm (patternRhoQ a b i : ℝ) (patternUQ a b i : ℝ)
    (patternVQ a b i : ℝ) (patternRhoQ a b (i + 1) : ℝ) (patternUQ a b (i + 1) : ℝ)
    (patternVQ a b (i + 1) : ℝ) (orbitFreeNodesQ a b i 0 : ℝ)
    (orbitFreeNodesQ a b i 1 : ℝ) (orbitFreeNodesQ a b i 2 : ℝ) = _
  simp only [patternRhoQ_cast, patternUQ_cast, patternVQ_cast, orbitFreeNodesQ_cast]
  rw [show orbitFreeNodes a b i 0 = pt a b i 1 from rfl,
    show orbitFreeNodes a b i 1 = pt a b i 2 from rfl,
    show orbitFreeNodes a b i 2 = pt a b i 3 from rfl, orbit_lineNorm_eq hba (by omega)]

/-- The common denominator `Q · H₃ · k₁` of the three curvature coordinates. -/
def jointLiftDenominator (Q : MvPolynomial (Fin 3) ℚ)
    (k : Fin 5 → MvPolynomial (Fin 3) ℚ) : MvPolynomial (Fin 3) ℚ :=
  Q * rawHankelThree (k 0) (k 1) (k 2) * k 1

/-- The numerators of `W₀, W₁, W₂, J`, in that order, over `jointLiftDenominator Q k`, where
`P / Q` is the reconstructed curvature `E₀` and `A` is the label `N₀`. -/
def jointLiftNumerators (P Q A J : MvPolynomial (Fin 3) ℚ)
    (k : Fin 5 → MvPolynomial (Fin 3) ℚ) : Fin 4 → MvPolynomial (Fin 3) ℚ :=
  let B0 := rawHankelThree (k 0) (k 1) (k 2)
  let B1 := rawHankelThree (k 1) (k 2) (k 3)
  let E := B1 * P - A * k 1 * Q
  ![E * k 1, -(k 0 * E + k 2 * P * B0), P * B0 * k 1,
    J * jointLiftDenominator Q k]

lemma rawHankelThree_degree {k0 k1 k2 : MvPolynomial (Fin 3) ℚ}
    (h0 : k0.totalDegree ≤ 1) (h1 : k1.totalDegree ≤ 1) (h2 : k2.totalDegree ≤ 1) :
    (rawHankelThree k0 k1 k2).totalDegree ≤ 3 := by
  unfold rawHankelThree
  fixed_dividend_mv_degree

/-- Uniform polynomial degree bounds for the common-denominator representation. -/
theorem jointLift_polynomial_degrees (P Q J : MvPolynomial (Fin 3) ℚ) (A : ℚ)
    (k : Fin 5 → MvPolynomial (Fin 3) ℚ) (hP : P.totalDegree ≤ 240)
    (hQ : Q.totalDegree ≤ 240) (hJ : J.totalDegree ≤ 3)
    (hk : ∀ j, (k j).totalDegree ≤ 1) :
    (jointLiftDenominator Q k).totalDegree ≤ 244 ∧
      (∀ j : Fin 3, (jointLiftNumerators P Q (C A) J k j.castSucc).totalDegree ≤ 244) ∧
      (jointLiftNumerators P Q (C A) J k 3).totalDegree ≤ 247 := by
  have hb0 := rawHankelThree_degree (hk 0) (hk 1) (hk 2)
  have hb1 := rawHankelThree_degree (hk 1) (hk 2) (hk 3)
  have hE : (rawHankelThree (k 1) (k 2) (k 3) * P - C A * k 1 * Q).totalDegree ≤ 243 := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by omega)
    · have h := totalDegree_mul (C A * k 1) Q
      have h' := totalDegree_mul (C A) (k 1)
      simp only [totalDegree_C] at h'
      have := hk 1
      omega
  have hd : (jointLiftDenominator Q k).totalDegree ≤ 244 := by
    unfold jointLiftDenominator
    have h := totalDegree_mul Q (rawHankelThree (k 0) (k 1) (k 2))
    have h' := totalDegree_mul (Q * rawHankelThree (k 0) (k 1) (k 2)) (k 1)
    have := hk 1
    omega
  refine ⟨hd, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp only [jointLiftNumerators, Fin.isValue, neg_add_rev, Fin.zero_eta,
      Fin.castSucc_zero, Fin.mk_one, Fin.castSucc_one, Fin.reduceFinMk, Fin.reduceCastSucc,
      cons_val_zero, cons_val_one, cons_val]
    · exact (totalDegree_mul _ _).trans (by have := hk 1; omega)
    · rw [← neg_add_rev, totalDegree_neg]
      apply (totalDegree_add _ _).trans
      apply max_le
      · exact (totalDegree_mul _ _).trans (by have := hk 0; omega)
      · have h := totalDegree_mul (k 2) P
        have h' := totalDegree_mul (k 2 * P) (rawHankelThree (k 0) (k 1) (k 2))
        have := hk 2
        omega
    · have h := totalDegree_mul P (rawHankelThree (k 0) (k 1) (k 2))
      have h' := totalDegree_mul (P * rawHankelThree (k 0) (k 1) (k 2)) (k 1)
      have := hk 1
      omega
  · change (J * jointLiftDenominator Q k).totalDegree ≤ 247
    exact (totalDegree_mul _ _).trans (by omega)

/-- At an orbit state, `H₃ = k₀ r₁ - k₁ r₀` and `H₃' = k₁ r₂ - k₂ r₁` for the raw rank-three
determinants `H₃, H₃'` of the gaps. -/
lemma orbit_curvature_raw_minors (a b i : ℕ) :
    rawHankelThree (kq a b i) (kq a b (i + 1)) (kq a b (i + 2)) =
      kq a b i * rq a b i 1 - kq a b (i + 1) * rq a b i 0 ∧
    rawHankelThree (kq a b (i + 1)) (kq a b (i + 2)) (kq a b (i + 3)) =
      kq a b (i + 1) * rq a b i 2 - kq a b (i + 2) * rq a b i 1 := by
  constructor <;> simp [rawHankelThree, kq, rq, sq, Nat.add_assoc] <;> ring

lemma eval_rawHankelThree (z : Fin 3 → ℚ) (x y w : MvPolynomial (Fin 3) ℚ) :
    eval z (rawHankelThree x y w) = rawHankelThree (eval z x) (eval z y) (eval z w) := by
  simp [rawHankelThree]

/-- The common denominator of the four joint coordinates for the pattern at state `i`. -/
def orbitJointDenominator (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  jointLiftDenominator (orbitLiftDenominatorQ a b i) (jointGapPolynomials a b i)

/-- The numerators of the four joint coordinates `W₀, W₁, W₂, J` for the pattern at state
`i`, over `orbitJointDenominator a b i`. -/
def orbitJointNumerators (a b i : ℕ) : Fin 4 → MvPolynomial (Fin 3) ℚ :=
  jointLiftNumerators (orbitLiftNumeratorQ a b i) (orbitLiftDenominatorQ a b i)
    (C (Lz a b i : ℚ)) (jointRankFivePolynomial a b i) (jointGapPolynomials a b i)

/-- The common denominator does not vanish at the free nodes of state `i`. -/
theorem orbitJointDenominator_eval_ne_zero {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    eval (orbitFreeNodesQ a b i) (orbitJointDenominator a b i) ≠ 0 := by
  simp only [orbitJointDenominator, jointLiftDenominator, map_mul, eval_rawHankelThree,
    jointGapPolynomials_eval hba hi, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero]
  have hp := rawHankelThree_pos_of_gaps
    (kq_pos (a := a) (b := b) (by omega : i + 1 < P a b))
    (kq_pos (a := a) (b := b) (by omega : i + 1 + 1 < P a b))
    (kq_pos (a := a) (b := b) (by omega : i + 2 + 1 < P a b))
  have hpQ : (0 : ℚ) < rawHankelThree (kq a b i : ℚ)
      (kq a b (i + 1) : ℚ) (kq a b (i + 2) : ℚ) := by
    unfold rawHankelThree at hp ⊢
    exact_mod_cast hp
  have hkQ : (0 : ℚ) < (kq a b (i + 1) : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1)
      (kq_pos (a := a) (b := b) (by omega : i + 1 + 1 < P a b)))
  exact mul_ne_zero (mul_ne_zero (orbitLift_evaluation hba hi).1 hpQ.ne') hkQ.ne'

/-- At the free nodes of state `i`, the first three joint coordinates take the integer values
of the curvature-minor vector `W = (D₁₂, -D₀₂, D₀₁)`. -/
theorem orbitJoint_curvature_evaluation {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (j : Fin 3) :
    eval (orbitFreeNodesQ a b i) (orbitJointNumerators a b i j.castSucc) /
      eval (orbitFreeNodesQ a b i) (orbitJointDenominator a b i) =
        (orbitCurvatureVector a b i j : ℚ) := by
  set q := eval (orbitFreeNodesQ a b i) (orbitLiftDenominatorQ a b i) with hqdef
  set p := eval (orbitFreeNodesQ a b i) (orbitLiftNumeratorQ a b i) with hpdef
  have hp : p = (integralLiftCoordinate a b i : ℚ) * q :=
    (eq_div_iff (orbitLift_evaluation hba hi).1).mp (orbitLift_evaluation hba hi).2 |>.symm
  have hd := orbitJointDenominator_eval_ne_zero hba hi
  have he := curvature_reconstruction_identity
    (fun j : Fin 3 => dq a b (i + j)) (fun j : Fin 3 => kq a b (i + j))
    (fun j : Fin 3 => rq a b i j)
  have hr := orbit_curvature_raw_minors a b i
  have he' : rawHankelThree (kq a b (i + 1)) (kq a b (i + 2)) (kq a b (i + 3)) *
      integralLiftCoordinate a b i - rawHankelThree (kq a b i) (kq a b (i + 1))
      (kq a b (i + 2)) * orbitCurvatureVector a b i 0 = Lz a b i * kq a b (i + 1) := by
    rw [hr.1, hr.2]
    have hdet : (Matrix.of ![fun j : Fin 3 => dq a b (i + j),
        fun j : Fin 3 => kq a b (i + j), fun j : Fin 3 => rq a b i j]).det = Lz a b i := by
      rw [← curvature_dot_row]
      exact orbitCurvature_dot_r a b i
    rw [hdet] at he
    simpa [integralLiftCoordinate, orbitCurvatureVector, curvatureVector] using he
  have heQ : rawHankelThree (kq a b (i + 1) : ℚ) (kq a b (i + 2) : ℚ)
      (kq a b (i + 3) : ℚ) * (integralLiftCoordinate a b i : ℚ) -
      rawHankelThree (kq a b i : ℚ) (kq a b (i + 1) : ℚ) (kq a b (i + 2) : ℚ) *
        (orbitCurvatureVector a b i 0 : ℚ) = (Lz a b i : ℚ) * (kq a b (i + 1) : ℚ) := by
    unfold rawHankelThree at he' ⊢
    exact_mod_cast he'
  have hzQ : (orbitCurvatureVector a b i 0 : ℚ) * (kq a b i : ℚ) +
      (orbitCurvatureVector a b i 1 : ℚ) * (kq a b (i + 1) : ℚ) +
      (integralLiftCoordinate a b i : ℚ) * (kq a b (i + 2) : ℚ) = 0 := by
    have hz := orbitCurvature_dot_gaps a b i
    rw [Fin.sum_univ_three, orbitCurvature_third] at hz
    exact_mod_cast hz
  apply (div_eq_iff hd).mpr
  fin_cases j <;> simp only [orbitJointNumerators, jointLiftNumerators, orbitJointDenominator,
    jointLiftDenominator, eval_rawHankelThree, jointGapPolynomials_eval hba hi, ← hpdef, ← hqdef,
    Fin.isValue, map_intCast, neg_add_rev, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Fin.castSucc_zero, Fin.castSucc_one, Fin.reduceCastSucc, cons_val_zero, cons_val_one, cons_val,
    map_add, map_neg, map_mul, map_sub, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod,
    Nat.reduceMod, add_zero]
  · rw [hp]
    linear_combination (q * (kq a b (i + 1) : ℚ)) * heQ
  · rw [hp]
    linear_combination -(q * (kq a b i : ℚ)) * heQ -
      (q * rawHankelThree (kq a b i : ℚ) (kq a b (i + 1) : ℚ) (kq a b (i + 2) : ℚ)) * hzQ
  · rw [hp, orbitCurvature_third]
    ring

/-- At the free nodes of state `i`, the fourth joint coordinate is the value of `J = N₀ Ψ`. -/
theorem orbitJoint_rankFive_evaluation {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    eval (orbitFreeNodesQ a b i) (orbitJointNumerators a b i 3) /
      eval (orbitFreeNodesQ a b i) (orbitJointDenominator a b i) =
        eval (orbitFreeNodesQ a b i) (jointRankFivePolynomial a b i) := by
  have hd := orbitJointDenominator_eval_ne_zero hba hi
  change eval _ (jointRankFivePolynomial a b i * orbitJointDenominator a b i) / _ = _
  rw [map_mul, mul_div_cancel_right₀ _ hd]

end
end PierceLengthBound.FixedDividend
