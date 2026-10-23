/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionNewton

/-! Initial forms of the polar resultant along arbitrary formal sections.
The proofs retain all higher-order terms of the section. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Matrix Polynomial
noncomputable section

/-- Remove exactly one formal parameter factor from every matrix entry. -/
def formalMatrixTail {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (PowerSeries R)) : Matrix (Fin n) (Fin n) (PowerSeries R) :=
  fun i j => PowerSeries.mk (fun k => PowerSeries.coeff (k + 1) (M i j))

lemma formalMatrix_eq_parameter_mul_tail {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (PowerSeries R))
    (hM : ∀ i j, PowerSeries.constantCoeff (M i j) = 0) :
    M = (PowerSeries.X : PowerSeries R) • formalMatrixTail M := by
  funext i j
  change M i j = PowerSeries.X * PowerSeries.mk (fun k => PowerSeries.coeff (k + 1) (M i j))
  have he := PowerSeries.eq_X_mul_shift_add_const (M i j)
  simpa only [hM i j, map_zero, add_zero] using he

/-- The determinant vanishes to at least the matrix size when all its entries vanish. -/
theorem formal_det_parameter_power {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (PowerSeries R))
    (hM : ∀ i j, PowerSeries.constantCoeff (M i j) = 0) :
    M.det = PowerSeries.X ^ n * (formalMatrixTail M).det := by
  conv_lhs => rw [formalMatrix_eq_parameter_mul_tail M hM]
  rw [Matrix.det_smul, Fintype.card_fin]

/-- The determinant's first possible coefficient is the determinant of the
linear coefficients. Arbitrary higher-order corrections do not affect it. -/
theorem formal_det_initial_coefficient {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (PowerSeries R))
    (hM : ∀ i j, PowerSeries.constantCoeff (M i j) = 0) :
    PowerSeries.coeff n M.det = Matrix.det (fun i j => PowerSeries.coeff 1 (M i j)) := by
  rw [formal_det_parameter_power M hM]
  have he := PowerSeries.coeff_X_pow_mul (formalMatrixTail M).det n 0
  rw [zero_add] at he
  rw [he, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    (PowerSeries.constantCoeff (R := R)).map_det]
  congr 1

theorem formal_det_lower_coefficients {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (PowerSeries R))
    (hM : ∀ i j, PowerSeries.constantCoeff (M i j) = 0) (k : ℕ) (hk : k < n) :
    PowerSeries.coeff k M.det = 0 := by
  rw [formal_det_parameter_power M hM, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hk]

/-- A cubic polynomial, with coefficients in ascending order. -/
def polarCubic {R : Type*} [CommRing R] (r : Fin 4 → R) : R[X] :=
  C (r 0) + C (r 1) * X + C (r 2) * X ^ 2 + C (r 3) * X ^ 3

/-- Adding the monic quartic to the cubic remainder gives a convenient
Bézout determinant without changing the resultant. -/
theorem polarCubic_resultant {R : Type*} [CommRing R] [Nontrivial R]
    (a r : Fin 4 → R) :
    resultant (monicQuartic a) (polarCubic r) 4 4 = (quarticBezout a (a + r)).det := by
  have hb : monicQuartic (a + r) = polarCubic r + monicQuartic a * 1 := by
    simp [monicQuartic, polarCubic]
    ring
  rw [← resultant_add_mul_right (monicQuartic a) (polarCubic r) 1 4 4
    (by simp) (by rw [monicQuartic_natDegree]), ← hb, resultant_monicQuartic]

lemma polarBezout_constantCoeff {R : Type*} [CommRing R]
    (a r : Fin 4 → PowerSeries R) (hr : ∀ j, PowerSeries.constantCoeff (r j) = 0) :
    ∀ i j, PowerSeries.constantCoeff (quarticBezout a (a + r) i j) = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [quarticBezout, hr] <;> ring

/-- Only the base quartic and the linear remainder contribute to the
first-order part of the Bézout matrix. -/
lemma polarBezout_linearCoeff {R : Type*} [CommRing R]
    (a r : Fin 4 → PowerSeries R) (hr : ∀ j, PowerSeries.constantCoeff (r j) = 0) :
    (fun i j => PowerSeries.coeff 1 (quarticBezout a (a + r) i j)) =
      quarticBezout (fun j => PowerSeries.constantCoeff (a j))
        (fun j => PowerSeries.constantCoeff (a j) + PowerSeries.coeff 1 (r j)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quarticBezout, PowerSeries.coeff_one_mul, hr] <;> ring

/-- The resultant has order at least four, with degree-four term equal to
the resultant of the base quartic and the first-order cubic remainder. -/
theorem polar_resultant_initial_form {R : Type*} [CommRing R] [Nontrivial R]
    (a r : Fin 4 → PowerSeries R) (hr : ∀ j, PowerSeries.constantCoeff (r j) = 0) :
    (∀ k < 4, PowerSeries.coeff k (resultant (monicQuartic a) (polarCubic r) 4 4) = 0) ∧
      PowerSeries.coeff 4 (resultant (monicQuartic a) (polarCubic r) 4 4) =
        resultant (monicQuartic (fun j => PowerSeries.constantCoeff (a j)))
          (polarCubic (fun j => PowerSeries.coeff 1 (r j))) 4 4 := by
  rw [polarCubic_resultant, polarCubic_resultant]
  constructor
  · intro k hk
    exact formal_det_lower_coefficients _ (polarBezout_constantCoeff a r hr) k hk
  · rw [formal_det_initial_coefficient _ (polarBezout_constantCoeff a r hr),
      polarBezout_linearCoeff a r hr]
    rfl

/-- Monomial coefficients of the Newton remainder. -/
def polarRemainderMonomialCoeffs {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (s : Fin 4 → R) : Fin 4 → R :=
  let t := polarRemainderCoefficients ρ u v ρ' u' v' s
  ![t 0, t 1 - s 0 * t 2 + s 0 * s 1 * t 3,
    t 2 - (s 0 + s 1) * t 3, t 3]

theorem polarNewtonRemainder_eq_cubic {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (s : Fin 4 → R) :
    polarNewtonRemainder ρ u v ρ' u' v' s =
      polarCubic (polarRemainderMonomialCoeffs ρ u v ρ' u' v' s) := by
  simp [polarNewtonRemainder, polarCubic, polarRemainderMonomialCoeffs]
  ring

lemma polarCubic_natDegree_le {R : Type*} [CommRing R] (r : Fin 4 → R) :
    (polarCubic r).natDegree ≤ 3 := by
  unfold polarCubic
  compute_degree

/-- The original curve resultant is exactly the resultant of the current
monic quartic and its cubic Newton remainder, with matching padded sizes. -/
theorem polar_curve_resultant_eq_cubic {R : Type*} [CommRing R] [Nontrivial R]
    (ρ u v ρ' u' v' : R) (x : Fin 3 → R) :
    let s := completeNodes ρ u v x
    MvPolynomial.eval x (curveResultant ρ u v ρ' u' v') =
      resultant (monicQuartic (firstNewtonCoeffs
        (fun j : Fin 4 => coeffs ρ u v j.castSucc) s))
        (polarCubic (polarRemainderMonomialCoeffs ρ u v ρ' u' v' s)) 4 4 := by
  dsimp only
  let s := completeNodes ρ u v x
  let p := firstNewtonQuartic (fun j : Fin 4 => coeffs ρ u v j.castSucc) s
  let r := polarCubic (polarRemainderMonomialCoeffs ρ u v ρ' u' v' s)
  have hp : p.natDegree ≤ 4 := by
    rw [show p = monicQuartic (firstNewtonCoeffs
      (fun j : Fin 4 => coeffs ρ u v j.castSucc) s) from firstNewtonQuartic_eq _ _,
      monicQuartic_natDegree]
  have he := polar_newton_division ρ u v ρ' u' v' s
  rw [polarNewtonRemainder_eq_cubic] at he
  have hZ : X * nextNewtonQuartic (fun j : Fin 4 => coeffs ρ' u' v' j.castSucc) s =
      r + p * (X + C (polarQuotientConstant v v' s)) := by
    change _ - _ * p = r at he
    linear_combination he
  rw [eval_curveResultant]
  change resultant p _ 4 5 = _
  rw [hZ, resultant_add_mul_right p r (X + C (polarQuotientConstant v v' s)) 4 5
    (by have : (X + C (polarQuotientConstant v v' s)).natDegree ≤ 1 := by compute_degree
        omega) hp]
  have hr : r.natDegree ≤ 4 := (polarCubic_natDegree_le _).trans (by omega)
  have hp4 : p.coeff 4 = 1 := by simp [p, firstNewtonQuartic_eq, monicQuartic_coeff]
  rw [show 5 = 4 + 1 by rfl, resultant_add_right_deg p r 4 4 1 hr, hp4,
    one_pow, one_mul, show p = monicQuartic (firstNewtonCoeffs
      (fun j : Fin 4 => coeffs ρ u v j.castSucc) s) from firstNewtonQuartic_eq _ _]

lemma formal_fourth_power_initial {R : Type*} [CommRing R]
    (D : PowerSeries R) (hD : PowerSeries.constantCoeff D = 0) :
    (∀ k < 4, PowerSeries.coeff k (D ^ 4) = 0) ∧
      PowerSeries.coeff 4 (D ^ 4) = PowerSeries.coeff 1 D ^ 4 := by
  let E := PowerSeries.mk (fun j => PowerSeries.coeff (j + 1) D)
  have he : D = PowerSeries.X * E := by
    simpa only [hD, map_zero, add_zero] using PowerSeries.eq_X_mul_shift_add_const D
  rw [he, mul_pow]
  constructor
  · intro k hk
    rw [PowerSeries.coeff_X_pow_mul']
    simp [Nat.not_le.mpr hk]
  · have h := PowerSeries.coeff_X_pow_mul (E ^ 4) 4 0
    rw [zero_add, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow] at h
    simpa using h

/-- The quartic initial coefficient of the complete fixed-dividend equation.
This statement applies to arbitrary formal sections and ignores no higher-order terms. -/
theorem polar_equation_initial_form {R : Type*} [CommRing R] [Nontrivial R]
    (a r : Fin 4 → PowerSeries R) (D : PowerSeries R) (A b : R)
    (hr : ∀ j, PowerSeries.constantCoeff (r j) = 0)
    (hD : PowerSeries.constantCoeff D = 0) :
    let F := PowerSeries.C A * resultant (monicQuartic a) (polarCubic r) 4 4 -
      PowerSeries.C b * D ^ 4
    (∀ k < 4, PowerSeries.coeff k F = 0) ∧
      PowerSeries.coeff 4 F = A * resultant
        (monicQuartic (fun j => PowerSeries.constantCoeff (a j)))
        (polarCubic (fun j => PowerSeries.coeff 1 (r j))) 4 4 -
          b * PowerSeries.coeff 1 D ^ 4 := by
  obtain ⟨hlower, hfirst⟩ := polar_resultant_initial_form a r hr
  obtain ⟨hDlower, hDfirst⟩ := formal_fourth_power_initial D hD
  dsimp only
  constructor
  · intro k hk
    simp [hlower k hk, hDlower k hk]
  · simp [hfirst, hDfirst]

end
end PierceLengthBound.FixedDividend
