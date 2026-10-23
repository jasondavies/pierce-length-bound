/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftMomentSystem
public import PierceLengthBound.IntegralLiftInvariant
public import PierceLengthBound.FixedDividendRationalOrbit
import all PierceLengthBound.FixedDividendTotalDegree

/-! The cofactor formula for the integral lift coordinate `I₃` on the pattern curve. The
moment system of an orbit state is the specialization at the free nodes of a polynomial matrix
`curveMomentSystem` over `ℚ[x₀, x₁, x₂]`, whose signed maximal minors `c_j` have total degree at
most `40`. Then `I₃ = a det(c_{j+k})_{j,k<3} (c₁ - c₀)³ / (c₁² - c₀c₂)³`, with numerator and
denominator `orbitLiftNumeratorQ`, `orbitLiftDenominatorQ` of total degree at most `240`, and
the denominator is nonzero at the free nodes of every orbit state. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Matrix MvPolynomial

/-- A determinant of multivariate polynomials of total degree at most `D` has total degree at
most `n D`. -/
lemma polynomial_det_totalDegree {R σ : Type*} [CommRing R] {n D : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (hM : ∀ i j, (M i j).totalDegree ≤ D) : M.det.totalDegree ≤ n * D := by
  classical
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro π _
  calc
    _ ≤ (∏ i, M (π i) i).totalDegree := totalDegree_smul_le _ _
    _ ≤ ∑ i, (M (π i) i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ _i : Fin n, D := Finset.sum_le_sum fun i _ => hM (π i) i
    _ = n * D := by simp

lemma momentCofactors_totalDegree {R σ : Type*} [CommRing R] {n D : ℕ}
    (M : Matrix (Fin n) (Fin (n + 1)) (MvPolynomial σ R))
    (hM : ∀ i j, (M i j).totalDegree ≤ D) (j : Fin (n + 1)) :
    (momentCofactors M j).totalDegree ≤ n * D := by
  induction j using Fin.cases with
  | zero => exact polynomial_det_totalDegree _ (fun i j => hM i j.succ)
  | succ j =>
    simp only [momentCofactors, Fin.cons_succ, Pi.neg_apply, totalDegree_neg,
      Matrix.cramer_apply]
    apply polynomial_det_totalDegree
    intro i k
    simp only [Matrix.updateCol_apply]
    split_ifs <;> first | exact hM i 0 | exact hM i k.succ

lemma map_momentCofactors {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (M : Matrix (Fin n) (Fin (n + 1)) R) (j : Fin (n + 1)) :
    f (momentCofactors M j) = momentCofactors (M.map f) j := by
  classical
  induction j using Fin.cases with
  | zero => exact f.map_det _
  | succ j =>
    simp only [momentCofactors, Fin.cons_succ, Pi.neg_apply, map_neg, Matrix.cramer_apply,
      f.map_det]
    congr 2
    ext i k
    simp only [RingHom.mapMatrix_apply, momentTail, Matrix.updateCol_apply, Matrix.map_apply]
    split_ifs <;> rfl


lemma momentSystem_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P Z : Polynomial R) :
    (momentSystem P Z).map f = momentSystem (P.map f) (Z.map f) := by
  ext i j
  change f ((momentSystemPolynomial P Z i).coeff j.val) =
    (momentSystemPolynomial (P.map f) (Z.map f) i).coeff j.val
  unfold momentSystemPolynomial
  rcases (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8).symm i with k | k
  all_goals
    simp only [shiftedMomentPolynomial, Sum.elim_inl, Sum.elim_inr]
    rw [← Polynomial.coeff_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]

lemma monicQuartic_coeff_totalDegree {R σ : Type*} [CommRing R]
    (c : Fin 4 → MvPolynomial σ R) {D : ℕ} (hc : ∀ i, (c i).totalDegree ≤ D) (j : ℕ) :
    ((monicQuartic c).coeff j).totalDegree ≤ D := by
  rw [monicQuartic_coeff]
  split_ifs <;> first | exact hc _ | simp

lemma firstNewtonQuartic_coeff_totalDegree {R σ : Type*} [CommRing R]
    (c : Fin 4 → R) (s : Fin 4 → MvPolynomial σ R)
    (hs : ∀ j, (s j).totalDegree ≤ 1) (j : ℕ) :
    ((firstNewtonQuartic (C ∘ c) s).coeff j).totalDegree ≤ 4 := by
  rw [firstNewtonQuartic_eq]
  apply monicQuartic_coeff_totalDegree
  intro i
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  fin_cases i <;> simp only [firstNewtonCoeffs, Fin.isValue, Function.comp_apply, Fin.zero_eta,
    Fin.mk_one, Fin.reduceFinMk, cons_val_zero, cons_val_one, cons_val, totalDegree_C, zero_le,
    ge_iff_le]
  all_goals fixed_dividend_mv_degree

lemma nextNewtonQuartic_coeff_totalDegree {R σ : Type*} [CommRing R]
    (c : Fin 4 → R) (s : Fin 4 → MvPolynomial σ R)
    (hs : ∀ j, (s j).totalDegree ≤ 1) (j : ℕ) :
    ((nextNewtonQuartic (C ∘ c) s).coeff j).totalDegree ≤ 4 := by
  rw [nextNewtonQuartic_eq]
  apply monicQuartic_coeff_totalDegree
  intro i
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  fin_cases i <;> simp only [nextNewtonCoeffs, Fin.isValue, Function.comp_apply, Fin.zero_eta,
    Fin.mk_one, Fin.reduceFinMk, cons_val_zero, cons_val_one, cons_val, ge_iff_le]
  all_goals fixed_dividend_mv_degree

lemma coeff_mul_X_pow_totalDegree {R σ : Type*} [CommRing R]
    (f : Polynomial (MvPolynomial σ R)) {D : ℕ} (hf : ∀ j, (f.coeff j).totalDegree ≤ D)
    (k j : ℕ) : ((f * Polynomial.X ^ k).coeff j).totalDegree ≤ D := by
  rw [Polynomial.coeff_mul_X_pow']
  split_ifs
  · exact hf _
  · simp

/-- The moment system built from the first Newton quartic and `X` times the next Newton
quartic. -/
def newtonMomentSystem {R : Type*} [CommRing R] (c e s : Fin 4 → R) :
    Matrix (Fin 8) (Fin 9) R :=
  momentSystem (firstNewtonQuartic c s) (Polynomial.X * nextNewtonQuartic e s)

lemma newtonMomentSystem_totalDegree {R σ : Type*} [CommRing R]
    (c e : Fin 4 → R) (s : Fin 4 → MvPolynomial σ R)
    (hs : ∀ j, (s j).totalDegree ≤ 1) (i : Fin 8) (j : Fin 9) :
    (newtonMomentSystem (C ∘ c) (C ∘ e) s i j).totalDegree ≤ 4 := by
  unfold newtonMomentSystem momentSystem momentSystemPolynomial
  rcases (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8).symm i with k | k
  · exact coeff_mul_X_pow_totalDegree _ (firstNewtonQuartic_coeff_totalDegree c s hs) _ _
  · change (((Polynomial.X * nextNewtonQuartic (C ∘ e) s) * Polynomial.X ^ k.val).coeff
      j.val).totalDegree ≤ 4
    apply coeff_mul_X_pow_totalDegree
    intro l
    rw [mul_comm Polynomial.X, ← pow_one Polynomial.X]
    exact coeff_mul_X_pow_totalDegree _ (nextNewtonQuartic_coeff_totalDegree e s hs) _ _

/-- The signed maximal minors of the Newton moment system with linear nodes have total degree
at most `40` (the entrywise bound four gives `32`). -/
theorem newtonMomentCofactors_totalDegree {R σ : Type*} [CommRing R]
    (c e : Fin 4 → R) (s : Fin 4 → MvPolynomial σ R)
    (hs : ∀ j, (s j).totalDegree ≤ 1) (j : Fin 9) :
    (momentCofactors (newtonMomentSystem (C ∘ c) (C ∘ e) s) j).totalDegree ≤ 40 := by
  exact (momentCofactors_totalDegree _ (newtonMomentSystem_totalDegree c e s hs) j).trans
    (by norm_num)


/-- The `3 × 3` Hankel matrix `(c_{j+k})` of a cofactor vector. -/
def cofactorHankel {R : Type*} (c : Fin 9 → R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => c ⟨i.val + j.val, by omega⟩

/-- The numerator `a det(cofactorHankel c) (c₁ - c₀)³` of the cofactor formula for `I₃`. -/
def cofactorLiftNumerator {R : Type*} [CommRing R] (a : R) (c : Fin 9 → R) : R :=
  a * (cofactorHankel c).det * (c 1 - c 0) ^ 3

/-- The denominator `(c₁² - c₀ c₂)³` of the cofactor formula for `I₃`. -/
def cofactorLiftDenominator {R : Type*} [CommRing R] (c : Fin 9 → R) : R :=
  (c 1 ^ 2 - c 0 * c 2) ^ 3

/-- For cofactors of total degree at most `40`, both polynomials in the cofactor formula for
`I₃` have total degree at most `240`. -/
theorem cofactorLift_totalDegree {R σ : Type*} [CommRing R]
    (a : R) (c : Fin 9 → MvPolynomial σ R) (hc : ∀ j, (c j).totalDegree ≤ 40) :
    (cofactorLiftNumerator (C a) c).totalDegree ≤ 240 ∧
      (cofactorLiftDenominator c).totalDegree ≤ 240 := by
  have hd : (c 1 - c 0).totalDegree ≤ 40 :=
    (totalDegree_sub _ _).trans (max_le (hc 1) (hc 0))
  have hv : (c 1 ^ 2 - c 0 * c 2).totalDegree ≤ 80 := by
    apply (totalDegree_sub _ _).trans
    exact max_le ((totalDegree_pow _ _).trans (by nlinarith [hc 1]))
      ((totalDegree_mul _ _).trans (by linarith [hc 0, hc 2]))
  constructor
  · unfold cofactorLiftNumerator
    have hdet : (cofactorHankel c).det.totalDegree ≤ 120 :=
      polynomial_det_totalDegree _ (fun i j => hc _)
    have hmul := totalDegree_mul (C a * (cofactorHankel c).det) ((c 1 - c 0) ^ 3)
    have hleft := totalDegree_mul (C a) (cofactorHankel c).det
    have hpow := totalDegree_pow (c 1 - c 0) 3
    rw [totalDegree_C] at hleft
    omega
  · exact (totalDegree_pow _ _).trans (by nlinarith)

/-- The cofactor formula at an orbit state with `i + 7 < P(a,b)`: for the cofactors `c` of the
orbit moment system, `cofactorLiftDenominator c ≠ 0` and
`I₃ = cofactorLiftNumerator a c / cofactorLiftDenominator c`. -/
theorem orbit_cofactorLift_reconstruction {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    let c := momentCofactors (orbitMomentSystem a b i)
    cofactorLiftDenominator c ≠ 0 ∧
      (integralLiftCoordinate a b i : ℝ) =
        cofactorLiftNumerator (a : ℝ) c / cofactorLiftDenominator c := by
  dsimp only
  let c := momentCofactors (orbitMomentSystem a b i)
  obtain ⟨_, _, hd, _, hmom⟩ := orbitMomentSystem_reconstruction hba hi
  change c 1 ^ 2 - c 0 * c 2 ≠ 0 at hd
  have hmatrix : hankel a b i 3 =
      ((c 1 - c 0) / (c 1 ^ 2 - c 0 * c 2)) • cofactorHankel c := by
    ext j k
    change hm a b i (j.val + k.val) = _
    rw [hmom ⟨j.val + k.val, by omega⟩]
    simp only [Matrix.smul_apply, smul_eq_mul, cofactorHankel]
    ring
  refine ⟨pow_ne_zero _ hd, ?_⟩
  rw [integralLiftCoordinate_eq hba (by omega), hankelInv, hmatrix, Matrix.det_smul]
  change (a : ℝ) * (((c 1 - c 0) / (c 1 ^ 2 - c 0 * c 2)) ^ 3 *
    (cofactorHankel c).det) = cofactorLiftNumerator (a : ℝ) c / cofactorLiftDenominator c
  simp only [cofactorLiftNumerator, cofactorLiftDenominator, div_pow]
  ring


lemma map_newtonMomentSystem {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c e s : Fin 4 → R) :
    (newtonMomentSystem c e s).map f = newtonMomentSystem (f ∘ c) (f ∘ e) (f ∘ s) := by
  unfold newtonMomentSystem
  rw [momentSystem_map, map_firstNewtonQuartic, Polynomial.map_mul,
    Polynomial.map_X, map_nextNewtonQuartic]

/-- The moment system of the pattern `(ρ, u, v; ρ', u', v')` as a polynomial matrix in the three
free nodes. -/
def curveMomentSystem {R : Type*} [CommRing R] (ρ u v ρ' u' v' : R) :
    Matrix (Fin 8) (Fin 9) (MvPolynomial (Fin 3) R) :=
  newtonMomentSystem (fun j : Fin 4 => C (coeffs ρ u v j.castSucc))
    (fun j : Fin 4 => C (coeffs ρ' u' v' j.castSucc))
    (completeNodes (C ρ) (C u) (C v) (fun j => X j))

lemma completeNodes_totalDegree {R : Type*} [Field R] (ρ u v : R) (j : Fin 4) :
    (completeNodes (C ρ) (C u) (C v) (fun j => X j) j).totalDegree ≤ 1 := by
  fin_cases j
  all_goals simp only [completeNodes, Fin.reduceFinMk, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  all_goals try exact le_of_eq (totalDegree_X _)
  change (fourthNode (C ρ) (C u) (C v) (X 0) (X 1) (X 2)).totalDegree ≤ 1
  have he : (fourthNode (C ρ) (C u) (C v) (X 0) (X 1) (X 2) : MvPolynomial (Fin 3) R) =
      C (ρ + u) * X 0 + C (-(u - v)) * X 1 + C (-(v - 1)) * X 2 := by
    simp [fourthNode]
    ring
  rw [he]
  exact linear_form_degree_le _ _ _

/-- The cofactors of the curve moment system have total degree at most `40`. -/
theorem curveMomentCofactors_totalDegree {R : Type*} [Field R]
    (ρ u v ρ' u' v' : R) (j : Fin 9) :
    (momentCofactors (curveMomentSystem ρ u v ρ' u' v') j).totalDegree ≤ 40 :=
  newtonMomentCofactors_totalDegree _ _ _ (completeNodes_totalDegree ρ u v) j

/-- Evaluating the curve moment system at `x` gives the Newton moment system at the complete
nodes of `x`. -/
theorem eval_curveMomentSystem {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (x : Fin 3 → R) :
    (curveMomentSystem ρ u v ρ' u' v').map (eval x) =
      newtonMomentSystem (fun j : Fin 4 => coeffs ρ u v j.castSucc)
        (fun j : Fin 4 => coeffs ρ' u' v' j.castSucc) (completeNodes ρ u v x) := by
  unfold curveMomentSystem
  rw [map_newtonMomentSystem]
  congr 1
  · funext j; simp
  · funext j; simp
  · funext j
    fin_cases j <;> simp [completeNodes, fourthNode]

/-- At the free nodes of an orbit state, the curve moment system of its pattern specializes
to the orbit moment system, so the cofactor formulas are uniform in the three free nodes. -/
theorem orbit_eval_curveMomentSystem {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    (curveMomentSystem (patternRho a b i) (patternU a b i) (patternV a b i)
      (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))).map
        (eval (orbitFreeNodes a b i)) = orbitMomentSystem a b i := by
  rw [eval_curveMomentSystem]
  have hn : completeNodes (patternRho a b i) (patternU a b i) (patternV a b i)
      (orbitFreeNodes a b i) = fun j : Fin 4 => pt a b i (j.val + 1) := by
    funext j
    fin_cases j <;> simp only [completeNodes, orbitFreeNodes, Fin.isValue, cons_val_zero,
      cons_val_one, cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_add, Nat.reduceAdd]
    exact orbit_fourthNode hba (by omega)
  rw [hn]
  unfold newtonMomentSystem orbitMomentSystem
  rw [orbitQuartic_newton, nextQuartic_newton]
  rfl

/-- The curve cofactors specialize to the cofactors of the orbit moment system. -/
theorem orbit_eval_curveMomentCofactors {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (j : Fin 9) :
    eval (orbitFreeNodes a b i)
      (momentCofactors (curveMomentSystem (patternRho a b i) (patternU a b i)
        (patternV a b i) (patternRho a b (i + 1)) (patternU a b (i + 1))
        (patternV a b (i + 1))) j) = momentCofactors (orbitMomentSystem a b i) j := by
  rw [map_momentCofactors, orbit_eval_curveMomentSystem hba hi]


lemma map_cofactorLiftNumerator {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : R) (c : Fin 9 → R) :
    f (cofactorLiftNumerator a c) = cofactorLiftNumerator (f a) (f ∘ c) := by
  simp only [cofactorLiftNumerator, map_mul, map_pow, map_sub, f.map_det]
  rfl

lemma map_cofactorLiftDenominator {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : Fin 9 → R) :
    f (cofactorLiftDenominator c) = cofactorLiftDenominator (f ∘ c) := by
  simp [cofactorLiftDenominator]

lemma map_curveMomentSystem {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ρ u v ρ' u' v' : R) :
    (curveMomentSystem ρ u v ρ' u' v').map (MvPolynomial.map f) =
      curveMomentSystem (f ρ) (f u) (f v) (f ρ') (f u') (f v') := by
  unfold curveMomentSystem
  rw [map_newtonMomentSystem]
  congr 1
  · funext j; fin_cases j <;> simp [coeffs]
  · funext j; fin_cases j <;> simp [coeffs]
  · funext j; fin_cases j <;> simp [completeNodes, fourthNode]

/-- The cofactors of the curve moment system of the rational pattern at `i`. -/
def orbitCurveCofactorsQ (a b i : ℕ) : Fin 9 → MvPolynomial (Fin 3) ℚ :=
  momentCofactors (curveMomentSystem (patternRhoQ a b i) (patternUQ a b i)
    (patternVQ a b i) (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1))
    (patternVQ a b (i + 1)))

/-- The numerator of the cofactor formula for `I₃`, as a polynomial in the free nodes. -/
def orbitLiftNumeratorQ (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  cofactorLiftNumerator (C (a : ℚ)) (orbitCurveCofactorsQ a b i)

/-- The denominator of the cofactor formula for `I₃`, as a polynomial in the free nodes. -/
def orbitLiftDenominatorQ (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  cofactorLiftDenominator (orbitCurveCofactorsQ a b i)

/-- The lift numerator and denominator have total degree at most `240`. -/
theorem orbitLift_polynomial_degrees (a b i : ℕ) :
    (orbitLiftNumeratorQ a b i).totalDegree ≤ 240 ∧
      (orbitLiftDenominatorQ a b i).totalDegree ≤ 240 :=
  cofactorLift_totalDegree _ _ (curveMomentCofactors_totalDegree _ _ _ _ _ _)

lemma orbit_eval_curveCofactorsQ_cast {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (j : Fin 9) :
    (eval (orbitFreeNodesQ a b i) (orbitCurveCofactorsQ a b i j) : ℝ) =
      momentCofactors (orbitMomentSystem a b i) j := by
  have hx : (algebraMap ℚ ℝ) ∘ orbitFreeNodesQ a b i = orbitFreeNodes a b i := by
    funext k
    exact orbitFreeNodesQ_cast a b i k
  change (algebraMap ℚ ℝ) (eval _ _) = _
  rw [MvPolynomial.map_eval, hx]
  unfold orbitCurveCofactorsQ
  rw [map_momentCofactors, map_curveMomentSystem]
  change eval (orbitFreeNodes a b i) (momentCofactors (curveMomentSystem
    (patternRhoQ a b i : ℝ) (patternUQ a b i : ℝ) (patternVQ a b i : ℝ)
    (patternRhoQ a b (i + 1) : ℝ) (patternUQ a b (i + 1) : ℝ)
    (patternVQ a b (i + 1) : ℝ)) j) = _
  simp only [patternRhoQ_cast, patternUQ_cast, patternVQ_cast]
  exact orbit_eval_curveMomentCofactors hba hi j

/-- At the free nodes of an orbit state with `i + 7 < P(a,b)`, the lift denominator is nonzero
and the positive integer `I₃(i)` is the quotient of the lift numerator and denominator. -/
theorem orbitLift_evaluation {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    eval (orbitFreeNodesQ a b i) (orbitLiftDenominatorQ a b i) ≠ 0 ∧
      (integralLiftCoordinate a b i : ℚ) =
        eval (orbitFreeNodesQ a b i) (orbitLiftNumeratorQ a b i) /
          eval (orbitFreeNodesQ a b i) (orbitLiftDenominatorQ a b i) := by
  let f : MvPolynomial (Fin 3) ℚ →+* ℝ :=
    (algebraMap ℚ ℝ).comp (eval (orbitFreeNodesQ a b i))
  have he : f ∘ orbitCurveCofactorsQ a b i = momentCofactors (orbitMomentSystem a b i) := by
    funext j
    exact orbit_eval_curveCofactorsQ_cast hba hi j
  have hn : f (orbitLiftNumeratorQ a b i) =
      cofactorLiftNumerator (a : ℝ) (momentCofactors (orbitMomentSystem a b i)) := by
    unfold orbitLiftNumeratorQ
    rw [map_cofactorLiftNumerator, he]
    simp [f]
  have hd : f (orbitLiftDenominatorQ a b i) =
      cofactorLiftDenominator (momentCofactors (orbitMomentSystem a b i)) := by
    unfold orbitLiftDenominatorQ
    rw [map_cofactorLiftDenominator, he]
  obtain ⟨hd0, hval⟩ := orbit_cofactorLift_reconstruction hba hi
  constructor
  · intro hz
    apply hd0
    rw [← hd]
    change (algebraMap ℚ ℝ) (eval _ _) = 0
    rw [hz, map_zero]
  · apply (algebraMap ℚ ℝ).injective
    rw [map_div₀]
    change (integralLiftCoordinate a b i : ℝ) = f (orbitLiftNumeratorQ a b i) /
      f (orbitLiftDenominatorQ a b i)
    rw [hn, hd]
    exact hval

/-- The lift denominator does not lie in an ideal whose zero locus contains the free nodes of
an orbit state. -/
theorem orbitLift_denominator_not_mem {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I) :
    orbitLiftDenominatorQ a b i ∉ I := by
  intro hd
  exact (orbitLift_evaluation hba hi).1 (hx _ hd)

end
end PierceLengthBound.FixedDividend
