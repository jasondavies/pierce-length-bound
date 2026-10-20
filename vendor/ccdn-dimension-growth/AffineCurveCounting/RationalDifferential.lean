module

public import AffineCurveCounting.AlgebraicDifferentialConstants
public import Mathlib

/-! The formal derivative on a rational function field and its constant field. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial

variable {K : Type*} [Field K]

/-- Quotient-rule numerator and denominator for formal rational differentiation. -/
def rationalDerivativeFraction (p q : K[X]) : RatFunc K :=
  (algebraMap K[X] (RatFunc K) p.derivative * algebraMap K[X] (RatFunc K) q -
    algebraMap K[X] (RatFunc K) p * algebraMap K[X] (RatFunc K) q.derivative) /
      (algebraMap K[X] (RatFunc K) q) ^ 2

lemma rationalDerivativeFraction_mul {p q a : K[X]} (hq : q ≠ 0) (ha : a ≠ 0) :
    rationalDerivativeFraction (a * p) (a * q) = rationalDerivativeFraction p q := by
  simp only [rationalDerivativeFraction, derivative_mul, map_add, map_mul]
  field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero ha]
  ring

/-- Formal rational differentiation, well-defined under changing fractions. -/
def rationalDerivative (x : RatFunc K) : RatFunc K :=
  x.liftOn' rationalDerivativeFraction (fun _hq _ha => rationalDerivativeFraction_mul _hq _ha)

lemma rationalDerivative_div (p q : K[X]) :
    rationalDerivative (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      rationalDerivativeFraction p q := by
  rw [rationalDerivative, RatFunc.liftOn'_div]
  intro p
  simp [rationalDerivativeFraction]

lemma rationalDerivative_polynomial (p : K[X]) :
    rationalDerivative (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) p.derivative := by
  simpa [rationalDerivativeFraction] using rationalDerivative_div p 1

lemma rationalDerivative_add (x y : RatFunc K) :
    rationalDerivative (x + y) = rationalDerivative x + rationalDerivative y := by
  induction x using RatFunc.induction_on with | _ p q hq
  induction y using RatFunc.induction_on with | _ r s hs
  have hq' := RatFunc.algebraMap_ne_zero hq
  have hs' := RatFunc.algebraMap_ne_zero hs
  rw [div_add_div _ _ hq' hs', ← map_mul, ← map_mul, ← map_add, ← map_mul,
    rationalDerivative_div, rationalDerivative_div, rationalDerivative_div]
  simp only [rationalDerivativeFraction, derivative_mul, map_add, map_mul]
  field_simp
  ring

lemma rationalDerivative_mul (x y : RatFunc K) :
    rationalDerivative (x * y) = x * rationalDerivative y + y * rationalDerivative x := by
  induction x using RatFunc.induction_on with | _ p q hq
  induction y using RatFunc.induction_on with | _ r s hs
  rw [div_mul_div_comm, ← map_mul, ← map_mul,
    rationalDerivative_div, rationalDerivative_div, rationalDerivative_div]
  simp only [rationalDerivativeFraction, derivative_mul, map_add, map_mul]
  field_simp
  ring

/-- Rational formal differentiation as a derivation over the coefficient field. -/
def rationalDerivation (K : Type*) [Field K] : Derivation K (RatFunc K) (RatFunc K) where
  toFun := rationalDerivative
  map_add' := rationalDerivative_add
  map_smul' c x := by
    rw [Algebra.smul_def, rationalDerivative_mul, Algebra.smul_def]
    have hc : rationalDerivative (algebraMap K (RatFunc K) c) = 0 := by
      rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), rationalDerivative_polynomial]
      simp
    simp only [hc, mul_zero, add_zero, RingHom.id_apply]
  map_one_eq_zero' := by
    simpa using rationalDerivative_polynomial (1 : K[X])
  leibniz' x y := rationalDerivative_mul x y

/-- The corresponding differential field structure; it is kept explicit to
avoid introducing a competing global instance on rational functions. -/
@[reducible]
def rationalDifferential (K : Type*) [Field K] : Differential (RatFunc K) := by
  let : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
  exact ⟨(rationalDerivation K).restrictScalars ℤ⟩

/-- In characteristic zero a rational function with zero formal derivative
is a constant. The proof uses the reduced numerator and denominator. -/
theorem rationalDerivative_eq_zero_iff [CharZero K] (x : RatFunc K) :
    rationalDerivative x = 0 ↔ x ∈ (algebraMap K (RatFunc K)).range := by
  constructor
  · intro hx
    have hfrac : rationalDerivativeFraction x.num x.denom = 0 := by
      rw [← rationalDerivative_div, x.num_div_denom]
      exact hx
    have hden := RatFunc.algebraMap_ne_zero x.denom_ne_zero
    have hnum : algebraMap K[X] (RatFunc K) x.num.derivative * algebraMap K[X] (RatFunc K) x.denom -
        algebraMap K[X] (RatFunc K) x.num * algebraMap K[X] (RatFunc K) x.denom.derivative = 0 :=
      (div_eq_zero_iff.mp hfrac).resolve_right (pow_ne_zero 2 hden)
    have he : x.num.derivative * x.denom = x.num * x.denom.derivative := by
      apply RatFunc.algebraMap_injective K
      simpa only [map_mul] using sub_eq_zero.mp hnum
    have hdvd : x.denom ∣ x.denom.derivative := by
      apply x.isCoprime_num_denom.symm.dvd_of_dvd_mul_left
      rw [← he]
      exact dvd_mul_left _ _
    have hdz : x.denom.derivative = 0 := by
      by_contra hn
      exact (not_le_of_gt (degree_derivative_lt x.denom_ne_zero)) (degree_le_of_dvd hdvd hn)
    have hnz : x.num.derivative = 0 := by
      rw [hdz, mul_zero] at he
      exact (mul_eq_zero.mp he).resolve_right x.denom_ne_zero
    refine ⟨x.num.coeff 0 / x.denom.coeff 0, ?_⟩
    conv_rhs => rw [← x.num_div_denom, eq_C_of_derivative_eq_zero hnz, eq_C_of_derivative_eq_zero hdz]
    simp only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, map_div₀]
  · rintro ⟨c, rfl⟩
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), rationalDerivative_polynomial]
    simp

/-- The chosen rational differential structure has exactly the coefficient
field as its constants. -/
theorem rationalDifferential_containConstants (K : Type*) [Field K] [CharZero K] :
    let := rationalDifferential K
    Differential.ContainConstants K (RatFunc K) := by
  let := rationalDifferential K
  constructor
  intro x hx
  exact (rationalDerivative_eq_zero_iff x).mp hx

/-- Constants of an algebraic differential extension of F(t), for
algebraically closed characteristic-zero F, belong to F. -/
theorem rational_algebraic_differential_constants
    {F L : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field L]
    [Algebra F L] [Algebra (RatFunc F) L] [IsScalarTower F (RatFunc F) L]
    [Differential L] [Algebra.IsAlgebraic (RatFunc F) L] :
    let := rationalDifferential F
    DifferentialAlgebra (RatFunc F) L → Differential.ContainConstants F L := by
  dsimp only
  let := rationalDifferential F
  intro h
  have := h
  have := rationalDifferential_containConstants F
  exact containConstants_of_algebraic (F := F) (K := RatFunc F) (L := L)

end
end AffineCurveCounting
