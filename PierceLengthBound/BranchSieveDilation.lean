/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveParameterSpecialization
public import CCDN.Noether.GenericPlaneStretch
import Mathlib.Tactic

/-! Simultaneous integer dilation `T_i ↦ g T_i` of the Hilbert parameters. It
preserves generic irreducibility and multiplies the coefficient height by at
most `g ^ d`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- The substitution `T_i ↦ g T_i`. -/
def branchDilation {σ R : Type*} [CommSemiring R] (g : R) :
    MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun i => C g * X i)

theorem branchDilation_monomial {σ R : Type*} [CommSemiring R]
    (g c : R) (s : σ →₀ ℕ) :
    branchDilation g (monomial s c) = monomial s (c * g ^ (s.sum fun _ e => e)) := by
  classical
  simp only [branchDilation, eval₂Hom_monomial, Finsupp.prod, mul_pow,
    Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [← mul_assoc, ← C_mul]
  exact monomial_eq.symm

theorem branchDilation_coeff {σ R : Type*} [CommSemiring R]
    (g : R) (p : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (branchDilation g p).coeff s = p.coeff s * g ^ (s.sum fun _ e => e) := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, branchDilation_monomial, coeff_sum, coeff_monomial]
  by_cases hs : s ∈ p.support
  · simp [hs]
  · have hz : p.coeff s = 0 := by simpa using hs
    simp [hs, hz]

theorem branchDilation_totalDegree_le {σ R : Type*} [CommSemiring R]
    (g : R) (p : MvPolynomial σ R) :
    (branchDilation g p).totalDegree ≤ p.totalDegree := by
  classical
  apply Finset.sup_mono
  intro s hs
  rw [mem_support_iff, branchDilation_coeff] at hs
  exact mem_support_iff.mpr (left_ne_zero_of_mul hs)

theorem branchDilation_height {σ : Type*} (g : ℕ) (hg : 1 ≤ g)
    (p : MvPolynomial σ ℤ) {d H : ℕ} (hd : p.totalDegree ≤ d)
    (hH : ∀ s, |p.coeff s| ≤ (H : ℤ)) (s : σ →₀ ℕ) :
    |(branchDilation (g : ℤ) p).coeff s| ≤ (H * g ^ d : ℕ) := by
  rw [branchDilation_coeff, abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℤ) ≤ g)]
  by_cases hs : p.coeff s = 0
  · simp only [hs, abs_zero, zero_mul]
    positivity
  · have hdegree : s.sum (fun _ e => e) ≤ d := (le_totalDegree (mem_support_iff.mpr hs)).trans hd
    push_cast
    apply mul_le_mul (hH s) ?_ (by positivity) (by positivity)
    exact pow_le_pow_right₀ (by exact_mod_cast hg) hdegree

/-- Dilation applied to every coefficient of a polynomial family. -/
def branchFamilyDilation {r : ℕ} (g : ℕ)
    (p : Polynomial (MvPolynomial (Fin r) ℤ)) : Polynomial (MvPolynomial (Fin r) ℤ) :=
  p.map (branchDilation (g : ℤ))

theorem branchFamilyDilation_eval {r : ℕ} (g : ℕ)
    (p : Polynomial (MvPolynomial (Fin r) ℤ)) (x : Fin r → ℤ) :
    branchFamilyEval x (branchFamilyDilation g p) =
      branchFamilyEval (fun j => (g : ℤ) * x j) p := by
  unfold branchFamilyEval branchFamilyDilation
  rw [Polynomial.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [branchDilation]
  · intro j
    simp [branchDilation]

theorem branchFamilyDilation_irreducible {r : ℕ} (g : ℕ) (hg : 0 < g)
    (p : Polynomial (MvPolynomial (Fin r) ℤ)) (hp : Irreducible (branchFamilyRational p)) :
    Irreducible (branchFamilyRational (branchFamilyDilation g p)) := by
  have hgQ : (g : ℚ) ≠ 0 := by positivity
  let e := CCDN.variableScaleEquiv ℚ (Fin r) (g : ℚ) hgQ
  have he : (MvPolynomial.map (Int.castRingHom ℚ)).comp (branchDilation (g : ℤ)) =
      e.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℚ)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [branchDilation, e, CCDN.variableScaleEquiv]
    · intro j
      simp [branchDilation, e, CCDN.variableScaleEquiv]
  unfold branchFamilyRational branchFamilyDilation
  rw [Polynomial.map_map, he, ← Polynomial.map_map]
  exact (MulEquiv.irreducible_iff (f := Polynomial.mapAlgEquiv e)).mpr hp

theorem branchFamilyDilation_degree_height {r d H : ℕ} (g : ℕ) (hg : 1 ≤ g)
    (p : Polynomial (MvPolynomial (Fin r) ℤ)) (hd : p.natDegree ≤ d)
    (hp : ∀ j, (p.coeff j).totalDegree ≤ d)
    (hH : ∀ j s, |(p.coeff j).coeff s| ≤ (H : ℤ)) :
    (branchFamilyDilation g p).natDegree ≤ d ∧
      (∀ j, ((branchFamilyDilation g p).coeff j).totalDegree ≤ d) ∧
      ∀ j s, |((branchFamilyDilation g p).coeff j).coeff s| ≤ (H * g ^ d : ℕ) := by
  refine ⟨Polynomial.natDegree_map_le.trans hd, ?_, ?_⟩
  · intro j
    rw [branchFamilyDilation, Polynomial.coeff_map]
    exact (branchDilation_totalDegree_le _ _).trans (hp j)
  · intro j s
    rw [branchFamilyDilation, Polynomial.coeff_map]
    exact branchDilation_height g hg _ (hp j) (hH j) s

end
end PierceLengthBound.FixedDividend
