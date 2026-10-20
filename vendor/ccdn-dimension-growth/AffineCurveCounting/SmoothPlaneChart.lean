module

public import AffineCurveCounting.SmoothLocalDeterminant
public import AffineCurveCounting.ResidueAggregation
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! The local smooth determinant bound in the bivariate coordinate-ring notation,
with either coordinate chosen as the nonsingular direction. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Matrix

/-- Make coordinate j the outer polynomial variable; the other is the parameter. -/
def planePolynomial (j : Fin 2) :
    MvPolynomial (Fin 2) ℤ →+* Polynomial (Polynomial ℤ) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    (fun k => if k = j then Polynomial.X else Polynomial.C Polynomial.X)

lemma planePolynomial_C (j : Fin 2) (c : ℤ) :
    planePolynomial j (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) := by
  simp [planePolynomial]

lemma planePolynomial_X (j k : Fin 2) : planePolynomial j (MvPolynomial.X k) =
    if k = j then Polynomial.X else Polynomial.C Polynomial.X := by
  simp [planePolynomial]

lemma planePolynomial_derivative (j : Fin 2) (f : MvPolynomial (Fin 2) ℤ) :
    (planePolynomial j f).derivative = planePolynomial j (MvPolynomial.pderiv j f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | mul_X f k hf =>
    by_cases h : k = j
    · subst k
      simp [map_mul, derivative_mul, planePolynomial_X, hf]
      ring
    · simp [map_mul, derivative_mul, planePolynomial_X, hf, h]
      ring

lemma planeEval_planePolynomial (j : Fin 2) (f : MvPolynomial (Fin 2) ℤ) (z : Fin 2 → ℤ) :
    planeEval (planePolynomial j f) (z j.rev) (z j) = MvPolynomial.eval z f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [planeEval]
  | add f g hf hg =>
    simpa only [map_add, planeEval, Polynomial.map_add, eval_add] using
      congrArg₂ (· + ·) hf hg
  | mul_X f k hf =>
    have hX : planeEval (planePolynomial j (MvPolynomial.X k)) (z j.rev) (z j) = z k := by
      fin_cases j <;> fin_cases k <;> simp [planePolynomial_X, planeEval]
    simpa only [map_mul, planeEval, Polynomial.map_mul, eval_mul, MvPolynomial.eval_X] using
      congrArg₂ (· * ·) hf hX

/-- Smooth local divisibility for arbitrary bivariate integer polynomial
functions, at a point where either chosen partial derivative is a unit mod p. -/
theorem smooth_plane_chart_det_divisibility {s : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (g : Fin s → MvPolynomial (Fin 2) ℤ)
    (z : Fin s → Fin 2 → ℤ) (p : ℤ) (a : Fin 2 → ℤ) (j : Fin 2)
    (hunit : IsCoprime p (MvPolynomial.eval a (MvPolynomial.pderiv j f)))
    (hz : ∀ i k, p ∣ z i k - a k) (hf : ∀ i, MvPolynomial.eval (z i) f = 0) :
    p ^ (s * (s - 1) / 2) ∣ (Matrix.of fun i k => MvPolynomial.eval (z i) (g k)).det := by
  have hu : IsCoprime p (planeEval (planePolynomial j f).derivative (a j.rev) (a j)) := by
    rwa [planePolynomial_derivative, planeEval_planePolynomial]
  have h := triangular_pow_dvd_smooth_plane_eval_det (planePolynomial j f)
    (fun k => planePolynomial j (g k)) (fun i => z i j.rev) (fun i => z i j)
    p (a j.rev) (a j) hu (fun i => hz i j.rev) (fun i => hz i j)
    (fun i => by rw [planeEval_planePolynomial]; exact hf i)
  simpa only [planeEval_planePolynomial] using h


lemma residueRows_label {c s : ℕ} (label : Fin s → Fin c) (i : Fin c)
    (j : Fin (Fintype.card {j : Fin s // label j = i})) :
    label (residueRows label i j) = i :=
  ((Fintype.equivFin {j : Fin s // label j = i}).symm j).property

/-- Smooth residue classes contribute their full sum of triangular exponents
to the gcd of maximal evaluation minors. Different classes may use different
nonsingular coordinate directions. -/
theorem smooth_plane_residue_minorGcd {c s N : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (g : Fin N → MvPolynomial (Fin 2) ℤ)
    (z : Fin s → Fin 2 → ℤ) (label : Fin s → Fin c)
    (p : ℤ) (a : Fin c → Fin 2 → ℤ) (j : Fin c → Fin 2)
    (hunit : ∀ i, IsCoprime p (MvPolynomial.eval (a i) (MvPolynomial.pderiv (j i) f)))
    (hz : ∀ i k, p ∣ z i k - a (label i) k)
    (hf : ∀ i, MvPolynomial.eval (z i) f = 0) :
    p ^ (∑ i : Fin c, let n := Fintype.card {k : Fin s // label k = i}; n * (n - 1) / 2) ∣
      Int.Matrix.minorGcd (Matrix.of fun i k => MvPolynomial.eval (z i) (g k)) := by
  apply residue_prime_powers_dvd_minorGcd _ label
  intro i cols
  apply smooth_plane_chart_det_divisibility f (fun k => g (cols k))
    (fun k => z (residueRows label i k)) p (a i) (j i) (hunit i)
  · intro k l
    simpa only [residueRows_label] using hz (residueRows label i k) l
  · intro k
    exact hf (residueRows label i k)

/-- The actual row partition gives the sharp leading quadratic lower bound
for the sum of the smooth local exponents. -/
theorem smooth_residue_exponent_lower {c s : ℕ} (label : Fin s → Fin c) (hc : 0 < c) :
    (s : ℝ) ^ 2 / (2 * c) - s ≤
      (∑ i : Fin c, (Fintype.card {k : Fin s // label k = i}) *
        ((Fintype.card {k : Fin s // label k = i}) - 1) / 2 : ℕ) := by
  let n := fun i => Fintype.card {k : Fin s // label k = i}
  have he (i : Fin c) : multiplicityExponent (n i) 1 = n i * (n i - 1) / 2 := by
    simp only [multiplicityExponent, Nat.div_one]
    rw [Fin.sum_univ_eq_sum_range (fun j => j) (n i), Finset.sum_range_id]
  have h := aggregate_exponent_lower Finset.univ n (fun _ => 1)
    (fun i => multiplicityExponent (n i) 1)
    (fun i _ => multiplicityExponent_lower_bound _ _ (by decide))
    (N := (c : ℝ)) (by exact_mod_cast hc) (by simp)
  simpa only [he, n, sum_residue_class_sizes] using h


/-- The geometric nonsingularity condition modulo a prime supplies the unit
hypothesis in the local determinant theorem. -/
theorem smooth_plane_mod_prime_det_divisibility {s p : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ) (g : Fin s → MvPolynomial (Fin 2) ℤ)
    (z : Fin s → Fin 2 → ℤ) (a : Fin 2 → ℤ) (j : Fin 2)
    (hderiv : (MvPolynomial.eval a (MvPolynomial.pderiv j f) : ZMod p) ≠ 0)
    (hz : ∀ i k, (p : ℤ) ∣ z i k - a k)
    (hf : ∀ i, MvPolynomial.eval (z i) f = 0) :
    (p : ℤ) ^ (s * (s - 1) / 2) ∣
      (Matrix.of fun i k => MvPolynomial.eval (z i) (g k)).det := by
  apply smooth_plane_chart_det_divisibility f g z (p : ℤ) a j _ hz hf
  exact (ZMod.coe_int_isUnit_iff_isCoprime _ p).mp (isUnit_iff_ne_zero.mpr hderiv)

end
end AffineCurveCounting
