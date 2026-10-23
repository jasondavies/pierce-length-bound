/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionBasePoint
public import PierceLengthBound.FixedDividendCurveEquations

/-! Newton division at the explicit polar base point. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial Matrix
noncomputable section

/-- Constant term in the quotient of the shifted quintic by the current quartic. -/
def polarQuotientConstant {R : Type*} [CommRing R] (v v' : R) (s : Fin 4 → R) : R :=
  v' - v - s 3

/-- Newton coefficients of the cubic remainder after monic polynomial division. -/
def polarRemainderCoefficients {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (s : Fin 4 → R) : Fin 4 → R :=
  let h := polarQuotientConstant v v' s
  ![-h * ρ, ρ' - ρ - (-ρ - u) * (s 0 + h),
    (-ρ' - u') - (-ρ - u) - (u - v) * (s 1 + h),
    (u' - v') - (u - v) - (v - 1) * (s 2 + h)]

/-- The cubic polynomial in the first four Newton basis elements. -/
def polarNewtonRemainder {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (s : Fin 4 → R) : R[X] :=
  let t := polarRemainderCoefficients ρ u v ρ' u' v' s
  C (t 0) + C (t 1) * X + C (t 2) * X * (X - C (s 0)) +
    C (t 3) * X * (X - C (s 0)) * (X - C (s 1))

/-- Exact Newton division, valid without imposing the quadric equation. -/
theorem polar_newton_division {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (s : Fin 4 → R) :
    X * nextNewtonQuartic (fun j : Fin 4 => coeffs ρ' u' v' j.castSucc) s -
      (X + C (polarQuotientConstant v v' s)) *
        firstNewtonQuartic (fun j : Fin 4 => coeffs ρ u v j.castSucc) s =
      polarNewtonRemainder ρ u v ρ' u' v' s := by
  simp [nextNewtonQuartic, firstNewtonQuartic, polarNewtonRemainder,
    polarRemainderCoefficients, polarQuotientConstant, coeffs]
  ring

/-- The four successive nodes of the polar base point. -/
def polarBaseNodes {K : Type*} [Field K] (ρ u v ρ' u' v' : K) : Fin 4 → K :=
  ![(ρ' - ρ) / (-ρ - u), ((-ρ' - u') - (-ρ - u)) / (u - v),
    ((u' - v') - (u - v)) / (v - 1), v' - v]

/-- The three independent gaps of the explicit base nodes. -/
def polarBaseGaps {K : Type*} [Field K] (ρ u v ρ' u' v' : K) : Fin 3 → K :=
  let s := polarBaseNodes ρ u v ρ' u' v'
  ![s 0, s 1 - s 0, s 2 - s 1]

lemma polarBaseGaps_polarVector {K : Type*} [Field K] (ρ u v ρ' u' v' : K)
    (h1 : -ρ - u ≠ 0) (h2 : u - v ≠ 0) (h3 : v - 1 ≠ 0) :
    polarVector ρ u v ρ' u' v' (polarBaseGaps ρ u v ρ' u' v') = 0 := by
  ext j
  fin_cases j <;>
    simp [polarVector, polarMatrix, polarLinear, polarBaseGaps, polarBaseNodes] <;>
    field_simp <;> ring

/-- The explicit node formula agrees with `-G⁻¹ ℓ`. -/
theorem polarBaseGaps_eq_basePoint {K : Type*} [Field K] (ρ u v ρ' u' v' : K)
    (hG : (polarMatrix ρ u v).det ≠ 0)
    (h1 : -ρ - u ≠ 0) (h2 : u - v ≠ 0) (h3 : v - 1 ≠ 0) :
    polarBaseGaps ρ u v ρ' u' v' = polarBasePoint ρ u v ρ' u' v' :=
  (polarVector_eq_zero_iff ρ u v ρ' u' v' hG _).mp
    (polarBaseGaps_polarVector ρ u v ρ' u' v' h1 h2 h3)

lemma polarBaseNodes_remainderCoefficients {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K)
    (h1 : -ρ - u ≠ 0) (h2 : u - v ≠ 0) (h3 : v - 1 ≠ 0) :
    polarRemainderCoefficients ρ u v ρ' u' v' (polarBaseNodes ρ u v ρ' u' v') = 0 := by
  ext j
  fin_cases j <;>
    simp [polarRemainderCoefficients, polarQuotientConstant, polarBaseNodes,
      h1, h2, h3, mul_div_cancel₀]

/-- At the polar base point the translated next quartic equals the current one,
so the quintic is precisely `X P`. -/
theorem polarBaseNodes_newton_identity {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K)
    (h1 : -ρ - u ≠ 0) (h2 : u - v ≠ 0) (h3 : v - 1 ≠ 0) :
    X * nextNewtonQuartic (fun j : Fin 4 => coeffs ρ' u' v' j.castSucc)
        (polarBaseNodes ρ u v ρ' u' v') =
      X * firstNewtonQuartic (fun j : Fin 4 => coeffs ρ u v j.castSucc)
        (polarBaseNodes ρ u v ρ' u' v') := by
  have he := polar_newton_division ρ u v ρ' u' v' (polarBaseNodes ρ u v ρ' u' v')
  rw [polarNewtonRemainder, polarBaseNodes_remainderCoefficients ρ u v ρ' u' v' h1 h2 h3] at he
  simpa [polarQuotientConstant, polarBaseNodes, sub_eq_zero] using he

/-- The explicit fourth node satisfies the original linear kernel relation. -/
lemma polarBaseNodes_completeNodes {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K)
    (h1 : -ρ - u ≠ 0) (h2 : u - v ≠ 0) (h3 : v - 1 ≠ 0) :
    completeNodes ρ u v (fun j : Fin 3 => polarBaseNodes ρ u v ρ' u' v' j.castSucc) =
      polarBaseNodes ρ u v ρ' u' v' := by
  ext j
  fin_cases j <;> simp [completeNodes, polarBaseNodes, fourthNode]
  field_simp
  ring

/-- The resultant vanishes at the explicit polar base point. -/
theorem polarBaseNodes_resultant_zero {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K)
    (h1 : -ρ - u ≠ 0) (h2 : u - v ≠ 0) (h3 : v - 1 ≠ 0) :
    MvPolynomial.eval (fun j : Fin 3 => polarBaseNodes ρ u v ρ' u' v' j.castSucc)
      (curveResultant ρ u v ρ' u' v') = 0 := by
  rw [eval_curveResultant, polarBaseNodes_completeNodes ρ u v ρ' u' v' h1 h2 h3,
    polarBaseNodes_newton_identity ρ u v ρ' u' v' h1 h2 h3]
  let p := firstNewtonQuartic (fun j : Fin 4 => coeffs ρ u v j.castSucc)
    (polarBaseNodes ρ u v ρ' u' v')
  have hp : p.natDegree ≤ 4 := by
    rw [show p = monicQuartic (firstNewtonCoeffs
      (fun j : Fin 4 => coeffs ρ u v j.castSucc)
      (polarBaseNodes ρ u v ρ' u' v')) from firstNewtonQuartic_eq _ _, monicQuartic_natDegree]
  change resultant p (X * p) 4 5 = 0
  rw [show X * p = 0 + p * X by ring,
    resultant_add_mul_right p 0 X 4 5 (by simp) hp]
  simp

/-- Every fixed-dividend curve contains the same explicit polar base point,
regardless of the dividend or leading label. -/
theorem polarBaseNodes_on_curve {K : Type*} [Field K]
    (ρ u v ρ' u' v' A a : K) (hG : (polarMatrix ρ u v).det ≠ 0)
    (h1 : -ρ - u ≠ 0) (h2 : u - v ≠ 0) (h3 : v - 1 ≠ 0) :
    let z := fun j : Fin 3 => polarBaseNodes ρ u v ρ' u' v' j.castSucc
    MvPolynomial.eval z (curveQuadratic ρ u v ρ' u' v') = 0 ∧
      MvPolynomial.eval z (curveEquation ρ u v ρ' u' v' A a) = 0 := by
  have hq := polarBasePoint_on_quadric ρ u v ρ' u' v' hG
  have hn := polarBasePoint_norm_zero ρ u v ρ' u' v' hG
  dsimp only at hq hn ⊢
  rw [← polarBaseGaps_eq_basePoint ρ u v ρ' u' v' hG h1 h2 h3] at hq hn
  have hcancel (x y : K) : x + (y - x) = y := by ring
  simp only [polarBaseGaps, Matrix.cons_val, hcancel] at hq hn
  constructor
  · rw [eval_curveQuadratic]
    exact hq
  · rw [curveEquation, map_sub, map_mul, MvPolynomial.eval_C, map_mul,
      MvPolynomial.eval_C, map_pow, eval_curveNorm,
      polarBaseNodes_resultant_zero ρ u v ρ' u' v' h1 h2 h3]
    have hn' : lineNorm ρ u v ρ' u' v'
        (polarBaseNodes ρ u v ρ' u' v' (Fin.castSucc 0))
        (polarBaseNodes ρ u v ρ' u' v' (Fin.castSucc 1))
        (polarBaseNodes ρ u v ρ' u' v' (Fin.castSucc 2)) = 0 := hn
    rw [hn']
    ring

end
end PierceLengthBound.FixedDividend
