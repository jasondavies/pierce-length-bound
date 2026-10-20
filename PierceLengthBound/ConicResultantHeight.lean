/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicIntegerValues
public import PierceLengthBound.Main

/-! Explicit resultant-height control and subpolynomial integer-value counts
for bounded-degree rational functions with bounded integer coefficients. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset Polynomial

/-- The permutation expansion bounds an integer determinant by `n! H^n`. -/
theorem integer_det_height {n H : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ i j, |M i j| ≤ H) : |M.det| ≤ (n.factorial : ℤ) * H ^ n := by
  rw [Matrix.det_apply']
  calc |∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) * ∏ i, M (σ i) i| ≤
      ∑ σ : Equiv.Perm (Fin n), |(Equiv.Perm.sign σ : ℤ) * ∏ i, M (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), (H : ℤ) ^ n := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, Equiv.Perm.sign_abs, one_mul, Finset.abs_prod]
      calc ∏ i, |M (σ i) i| ≤ ∏ _i : Fin n, (H : ℤ) :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hM (σ i) i)
        _ = _ := by simp
    _ = _ := by simp [Fintype.card_perm]

/-- Every Sylvester matrix entry is a coefficient of one polynomial, or zero. -/
lemma sylvester_entry_height {F G : ℤ[X]} {H m n : ℕ}
    (hF : ∀ i, |F.coeff i| ≤ H) (hG : ∀ i, |G.coeff i| ≤ H) :
    ∀ i j, |F.sylvester G m n i j| ≤ H := by
  intro i j
  induction j using Fin.addCases with
  | left j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs <;> first | exact hG _ | simpa only [abs_zero] using (Nat.cast_nonneg H : (0 : ℤ) ≤ H)
  | right j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs <;> first | exact hF _ | simpa only [abs_zero] using (Nat.cast_nonneg H : (0 : ℤ) ≤ H)

/-- Fixed-degree integer polynomials have polynomially bounded resultants. -/
theorem resultant_height {F G : ℤ[X]} {H d : ℕ} (hH : 1 ≤ H)
    (hFd : F.natDegree ≤ d) (hGd : G.natDegree ≤ d)
    (hF : ∀ i, |F.coeff i| ≤ H) (hG : ∀ i, |G.coeff i| ≤ H) :
    (F.resultant G).natAbs ≤ (2 * d).factorial * H ^ (2 * d) := by
  have h := integer_det_height (F.sylvester G F.natDegree G.natDegree)
    (sylvester_entry_height hF hG)
  have hn : F.natDegree + G.natDegree ≤ 2 * d := by omega
  have hn' : (F.resultant G).natAbs ≤
      (F.natDegree + G.natDegree).factorial * H ^ (F.natDegree + G.natDegree) := by
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  exact hn'.trans (Nat.mul_le_mul (Nat.factorial_le hn) (Nat.pow_le_pow_right hH hn))

/-- Integer values of a rational function are uniformly controlled by its
fixed degree and coefficient height, without a bound on the parameter range. -/
theorem integer_values_card_of_height {F G : ℤ[X]} {H d : ℕ} (hH : 1 ≤ H)
    (hFd : F.natDegree ≤ d) (hGd : G.natDegree ≤ d) (hGpos : 0 < G.natDegree)
    (hF : ∀ i, |F.coeff i| ≤ H) (hG : ∀ i, |G.coeff i| ≤ H)
    (hcop : IsCoprime (F.map (Int.castRingHom ℚ)) (G.map (Int.castRingHom ℚ)))
    (S : Finset ℤ) (hdiv : ∀ t ∈ S, G.eval t ∣ F.eval t) :
    S.card ≤ 2 * d * tauMax ((2 * d).factorial * H ^ (2 * d)) := by
  exact (integer_values_card F G hGpos hcop S hdiv).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ hGd)
      (tau_le_tauMax (resultant_height hH hFd hGd hF hG)))

/-- The explicit divisor slack is subpolynomial for every fixed polynomial
coefficient-height bound. -/
def integerValueSlack (d C e a : ℕ) : ℕ :=
  2 * d * tauMax ((2 * d).factorial * C ^ (2 * d) * a ^ (e * (2 * d)))

theorem integerValueSlack_slow (d C e : ℕ) : SlowGrowth (integerValueSlack d C e) := by
  have hc : SlowGrowth (fun _ : ℕ => 2 * d) := by
    intro η hη
    refine ⟨2 * d + 1, by positivity, fun a ha => ?_⟩
    have hp := Real.one_le_rpow (by exact_mod_cast ha : (1 : ℝ) ≤ a) hη.le
    push_cast
    nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
  exact hc.mul (tauMax_slow ((2 * d).factorial * C ^ (2 * d)) (e * (2 * d)))

/-- Polynomial coefficient height yields the required subpolynomial count. -/
theorem integer_values_card_polynomial_height {F G : ℤ[X]} {d C e a : ℕ}
    (hC : 1 ≤ C) (ha : 1 ≤ a) (hFd : F.natDegree ≤ d) (hGd : G.natDegree ≤ d)
    (hGpos : 0 < G.natDegree)
    (hF : ∀ i, |F.coeff i| ≤ (C * a ^ e : ℕ))
    (hG : ∀ i, |G.coeff i| ≤ (C * a ^ e : ℕ))
    (hcop : IsCoprime (F.map (Int.castRingHom ℚ)) (G.map (Int.castRingHom ℚ)))
    (S : Finset ℤ) (hdiv : ∀ t ∈ S, G.eval t ∣ F.eval t) :
    S.card ≤ integerValueSlack d C e a := by
  have hH : 1 ≤ C * a ^ e := by
    have hp : 1 ≤ a ^ e := Nat.one_le_pow _ _ ha
    nlinarith
  have h := integer_values_card_of_height hH hFd hGd hGpos hF hG hcop S hdiv
  simpa only [integerValueSlack, mul_pow, ← pow_mul, mul_assoc] using h

end PierceLengthBound.FixedDividend
