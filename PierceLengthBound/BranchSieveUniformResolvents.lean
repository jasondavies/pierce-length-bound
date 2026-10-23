/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveResolventHeight
public import PierceLengthBound.BranchSieveIntegralResolvent
public import PierceLengthBound.BranchSieveNestedFactorHeight
import Mathlib.Tactic

/-! Uniform degree and polynomial height bounds for the integral coefficient
minimal polynomials that witness reducible specializations. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

/-- The signed coefficients of `p` keep the coefficient degree bound. -/
theorem branch_signed_coefficients_degree (p : ℤ[X][X]) (n D : ℕ)
    (hD : ∀ j, (p.coeff j).natDegree ≤ D) (i : Fin n) :
    (branchSignedCoefficients p n i).natDegree ≤ D := by
  unfold branchSignedCoefficients
  have he : (-1 : ℤ[X]) ^ (i.val + 1) = C ((-1 : ℤ) ^ (i.val + 1)) := by simp
  rw [he]
  exact (natDegree_C_mul_le _ _).trans (hD _)

/-- The signed coefficients of `p` keep the coefficient height bound. -/
theorem branch_signed_coefficients_height (p : ℤ[X][X]) (n H : ℕ)
    (hH : ∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ)) (i : Fin n) (j : ℕ) :
    |(branchSignedCoefficients p n i).coeff j| ≤ (H : ℤ) := by
  unfold branchSignedCoefficients
  have he : (-1 : ℤ[X]) ^ (i.val + 1) = C ((-1 : ℤ) ^ (i.val + 1)) := by simp
  rw [he, coeff_C_mul, abs_mul, abs_pow]
  simpa using hH (n - (i.val + 1)) j

/-- The universal resolvents of all factor-coefficient expressions, evaluated at
the signed coefficients of `p`, are monic with total degree at most `M` and
height at most `C (H + 1)^E`, with constants depending only on `n` and `D`. -/
theorem branch_uniform_resolvent_bounds (n D : ℕ) :
    ∃ M E C : ℕ, 0 < C ∧ ∀ (p : ℤ[X][X]) (H : ℕ),
      (∀ j, (p.coeff j).natDegree ≤ D) →
      (∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ)) →
      ∀ (s : Finset (Fin n)) (j : ℕ), j ≤ n →
      let Q := (branchUniversalResolvent (branchFactorCoefficientExpression s j)).map
        (MvPolynomial.aeval (branchSignedCoefficients p n)).toRingHom
      Q.Monic ∧ CCDN.bivariateTotalDegree Q ≤ M ∧
        ∀ i k, |(Q.coeff i).coeff k| ≤ (C * (H + 1) ^ E : ℕ) := by
  classical
  let I := Finset (Fin n) × Fin (n + 1)
  have hex (x : I) := branch_fixed_resolvent_substitution_bound
    (branchUniversalResolvent (branchFactorCoefficientExpression x.1 x.2.val)) D
  choose m e c hc hb using hex
  let M := univ.sup m
  let E := univ.sup e
  let C := univ.sup c + 1
  refine ⟨M, E, C, by dsimp [C]; omega, ?_⟩
  intro p H hD hH s j hj
  let x : I := (s, ⟨j, by omega⟩)
  have hv := branch_signed_coefficients_degree p n D hD
  have hh := branch_signed_coefficients_height p n H hH
  have hm := hb x H (branchSignedCoefficients p n) hv hh
  have heval : (MvPolynomial.aeval (R := ℤ) (branchSignedCoefficients p n)).toRingHom =
      MvPolynomial.eval₂Hom Polynomial.C (branchSignedCoefficients p n) := by
    ext z i <;> simp
  dsimp only
  refine ⟨(branchUniversalResolvent_monic _).map _, ?_, ?_⟩
  · rw [heval]
    exact hm.1.trans (le_sup (mem_univ x))
  · intro i k
    rw [heval]
    apply (hm.2 i k).trans
    have hE : e x ≤ E := le_sup (mem_univ x)
    have hC : c x ≤ C := (le_sup (mem_univ x)).trans (Nat.le_succ _)
    exact_mod_cast Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) hE)

/-- Minimal polynomials over `ℤ[X]` of the coefficients of monic factors of `p`
have total degree and height bounded uniformly in terms of `n`, `D` and `H`. -/
theorem branch_uniform_integral_minpoly_bounds (n D : ℕ) :
    ∃ M E C : ℕ, 0 < C ∧ ∀ (L : Type*) [Field L]
      [Algebra ℤ[X] L] [FaithfulSMul ℤ[X] L],
      ∀ (p : ℤ[X][X]), p.Monic → p.natDegree = n →
      (p.map (algebraMap ℤ[X] L)).Splits →
      ∀ H : ℕ, (∀ j, (p.coeff j).natDegree ≤ D) →
      (∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ)) →
      ∀ q : Polynomial (integralClosure ℤ[X] L), q.Monic →
      q ∣ p.map (algebraMap ℤ[X] (integralClosure ℤ[X] L)) →
      ∀ j : ℕ, j ≤ n →
      CCDN.bivariateTotalDegree (minpoly ℤ[X] (q.coeff j)) ≤ M ∧
      ∀ i k, |((minpoly ℤ[X] (q.coeff j)).coeff i).coeff k| ≤
        (C * (H + 1) ^ E : ℕ) := by
  obtain ⟨M, E, C, hC, hb⟩ := branch_uniform_resolvent_bounds n D
  let K := 2 ^ ((M + 1) * M) * ((M + 1) * M + 1) * (M + 1) ^ 2
  refine ⟨M, E, K * C, by dsimp [K]; positivity, ?_⟩
  intro L _ _ _ p hp hn hsplit H hD hH q hq hdiv j hj
  have h := branch_integral_factor_universal_divisor p hp hsplit q hq hdiv
  rw [hn] at h
  obtain ⟨s, hs⟩ := h
  obtain ⟨hmonic, hdegree, hheight⟩ := hb p H hD hH s j hj
  refine ⟨(branch_nested_totalDegree_le_of_dvd hmonic.ne_zero (hs j)).trans hdegree, ?_⟩
  intro i k
  have hh := branch_nested_factor_coeff_height _ hmonic.ne_zero hdegree hheight
    _ (hs j) i k
  simpa only [K, mul_assoc] using hh

end
end PierceLengthBound.FixedDividend
