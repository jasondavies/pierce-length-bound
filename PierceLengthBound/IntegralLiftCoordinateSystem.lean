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

/-! Polynomial cofactor coordinates, their degree bounds, and specialization.
These are coordinate formulas, not a graph-degree or point-counting theorem. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Matrix MvPolynomial

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
  fin_cases i <;> simp [firstNewtonCoeffs]
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
  fin_cases i <;> simp [nextNewtonCoeffs]
  all_goals fixed_dividend_mv_degree

lemma coeff_mul_X_pow_totalDegree {R σ : Type*} [CommRing R]
    (f : Polynomial (MvPolynomial σ R)) {D : ℕ} (hf : ∀ j, (f.coeff j).totalDegree ≤ D)
    (k j : ℕ) : ((f * Polynomial.X ^ k).coeff j).totalDegree ≤ D := by
  rw [Polynomial.coeff_mul_X_pow']
  split_ifs
  · exact hf _
  · simp

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

/-- The uniform degree 40 used in the candidate follows even from the rough
degree-four bound on each matrix entry (which gives degree 32). -/
theorem newtonMomentCofactors_totalDegree {R σ : Type*} [CommRing R]
    (c e : Fin 4 → R) (s : Fin 4 → MvPolynomial σ R)
    (hs : ∀ j, (s j).totalDegree ≤ 1) (j : Fin 9) :
    (momentCofactors (newtonMomentSystem (C ∘ c) (C ∘ e) s) j).totalDegree ≤ 40 := by
  exact (momentCofactors_totalDegree _ (newtonMomentSystem_totalDegree c e s hs) j).trans
    (by norm_num)


def cofactorHankel {R : Type*} (c : Fin 9 → R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => c ⟨i.val + j.val, by omega⟩

def cofactorLiftNumerator {R : Type*} [CommRing R] (a : R) (c : Fin 9 → R) : R :=
  a * (cofactorHankel c).det * (c 1 - c 0) ^ 3

def cofactorLiftDenominator {R : Type*} [CommRing R] (c : Fin 9 → R) : R :=
  (c 1 ^ 2 - c 0 * c 2) ^ 3

/-- Both polynomials in the rational expression for I3 have uniformly bounded
multivariate degree. This does not assert the degree of their graph. -/
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

/-- Actual reconstruction of the integral lift coordinate using the explicit
cofactor polynomials; its denominator is nonzero at every supported state. -/
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

theorem curveMomentCofactors_totalDegree {R : Type*} [Field R]
    (ρ u v ρ' u' v' : R) (j : Fin 9) :
    (momentCofactors (curveMomentSystem ρ u v ρ' u' v') j).totalDegree ≤ 40 :=
  newtonMomentCofactors_totalDegree _ _ _ (completeNodes_totalDegree ρ u v) j

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

/-- The polynomial matrix specializes to the actual moment system, so the
cofactor formulas are uniform in the three free node coordinates. -/
theorem orbit_eval_curveMomentSystem {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    (curveMomentSystem (patternRho a b i) (patternU a b i) (patternV a b i)
      (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))).map
        (eval (orbitFreeNodes a b i)) = orbitMomentSystem a b i := by
  rw [eval_curveMomentSystem]
  have hn : completeNodes (patternRho a b i) (patternU a b i) (patternV a b i)
      (orbitFreeNodes a b i) = fun j : Fin 4 => pt a b i (j.val + 1) := by
    funext j
    fin_cases j <;> simp [completeNodes, orbitFreeNodes]
    exact orbit_fourthNode hba (by omega)
  rw [hn]
  unfold newtonMomentSystem orbitMomentSystem
  rw [orbitQuartic_newton, nextQuartic_newton]
  rfl

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

def orbitCurveCofactorsQ (a b i : ℕ) : Fin 9 → MvPolynomial (Fin 3) ℚ :=
  momentCofactors (curveMomentSystem (patternRhoQ a b i) (patternUQ a b i)
    (patternVQ a b i) (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1))
    (patternVQ a b (i + 1)))

def orbitLiftNumeratorQ (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  cofactorLiftNumerator (C (a : ℚ)) (orbitCurveCofactorsQ a b i)

def orbitLiftDenominatorQ (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  cofactorLiftDenominator (orbitCurveCofactorsQ a b i)

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

/-- The actual positive integer I3 is the evaluation of this rational function
on the rational component coordinates. No reconstruction hypothesis remains. -/
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

/-- A component through the supported orbit point cannot be contained in the
pole-denominator zero set. This supplies the proper-section prerequisite. -/
theorem orbitLift_denominator_not_mem {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I) :
    orbitLiftDenominatorQ a b i ∉ I := by
  intro hd
  exact (orbitLift_evaluation hba hi).1 (hx _ hd)


/-- The lift is nonzero as a rational function on every retained component,
by its strictly positive value at the supporting orbit point. -/
theorem orbitLift_numerator_not_mem {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I) :
    orbitLiftNumeratorQ a b i ∉ I := by
  intro hn
  have hval := (orbitLift_evaluation hba hi).2
  rw [hx _ hn, zero_div] at hval
  have hp : (1 : ℚ) ≤ (integralLiftCoordinate a b i : ℚ) := by
    exact_mod_cast integralLiftCoordinate_pos hba (by omega : i + 3 < P a b)
  linarith

end
end PierceLengthBound.FixedDividend
