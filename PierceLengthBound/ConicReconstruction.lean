/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendIdentity

/-! Rational reconstruction identities from the normalized first two moments.
The cofactor construction and its parameter-height bounds remain separate tasks. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial

/-- The eight shifted orthogonality rows admit no nontrivial relation.
This is the polynomial divisibility step in the cofactor reconstruction. -/
theorem shifted_quartics_independent {K : Type*} [Field K] {P Z U V : K[X]}
    (hP : P ≠ 0) (hcop : IsCoprime P Z) (hV : V.natDegree < P.natDegree)
    (hrel : U * P + V * Z = 0) : U = 0 ∧ V = 0 := by
  have hd : P ∣ V * Z := by
    refine ⟨-U, ?_⟩
    linear_combination hrel
  have hv : V = 0 := by
    by_contra hv
    exact (not_le_of_gt hV) (Polynomial.natDegree_le_of_dvd
      (hcop.dvd_of_dvd_mul_right hd) hv)
  rw [hv, zero_mul, add_zero] at hrel
  exact ⟨(mul_eq_zero.mp hrel).resolve_right hP, hv⟩

/-- Positive variance rules out the pole in the quotient reconstruction formula. -/
lemma normalized_first_ne_one {n₀ n₁ n₂ q : ℝ} (h₀ : 0 < n₀)
    (hv : n₁ ^ 2 < n₀ * n₂) (h1 : q * n₀ + n₁ = 1) (h2 : q * n₁ + n₂ = 1) :
    n₁ / n₀ ≠ 1 := by
  intro he
  have hn : n₁ = n₀ := (div_eq_one_iff_eq h₀.ne').mp he
  rw [hn] at h1 h2 hv
  have : n₂ = n₀ := by linarith
  nlinarith

/-- Algebraic reconstruction of the quotient from normalized moments. -/
theorem quotient_from_normalized_moments {n₀ n₁ n₂ q : ℝ} (h₀ : 0 < n₀)
    (hv : n₁ ^ 2 < n₀ * n₂) (h1 : q * n₀ + n₁ = 1) (h2 : q * n₁ + n₂ = 1) :
    q = (n₁ / n₀ - n₂ / n₀) / (n₁ / n₀ - 1) := by
  apply (eq_div_iff (sub_ne_zero.mpr (normalized_first_ne_one h₀ hv h1 h2))).mpr
  field_simp
  linear_combination h2 - h1

/-- Strict variance of the actual positive moment model. -/
lemma orbit_moment_variance {a b i : ℕ} (hba : b < a) (hi : i + 1 < P a b) :
    hm a b i 1 ^ 2 < hm a b i 0 * hm a b i 2 := by
  have h := (hankel_posDef hba (i := i) (r := 2) (by omega) (by omega)).det_pos
  rw [Matrix.det_fin_two] at h
  simp only [hankel, Matrix.of_apply, Fin.val_zero, Fin.val_one, zero_add, add_zero] at h
  norm_num at h
  nlinarith

/-- The two normalizations hold at every sufficiently supported actual state. -/
lemma orbit_moment_normalizations {a b i : ℕ} (hba : b < a) (hi : i + 1 < P a b) :
    (qq a b i : ℝ) * hm a b i 0 + hm a b i 1 = 1 ∧
      (qq a b i : ℝ) * hm a b i 1 + hm a b i 2 = 1 := by
  have h1 := nuF_mul_X_add hba i 1
  have h2 := nuF_mul_X_add hba i X
  rw [muF_one hba (by omega), one_mul] at h1
  rw [muF_X hba hi, show (X : ℝ[X]) * X = X ^ 2 by ring] at h2
  have hz : nuF a b i 1 = hm a b i 0 := by simpa using nuF_X_pow (a := a) (b := b) i 0
  have ho : nuF a b i X = hm a b i 1 := by simpa using nuF_X_pow (a := a) (b := b) i 1
  rw [hz, ho] at h1
  rw [ho, nuF_X_pow] at h2
  constructor <;> linarith

/-- The candidate's reconstruction formulas, now for actual orbit moments. -/
theorem orbit_rational_reconstruction {a b i : ℕ} (hba : b < a) (hi : i + 1 < P a b) :
    let m₁ := hm a b i 1 / hm a b i 0
    let m₂ := hm a b i 2 / hm a b i 0
    m₁ ≠ 1 ∧ (qq a b i : ℝ) = (m₁ - m₂) / (m₁ - 1) ∧
      (orb a b i : ℝ) = a / ((qq a b i : ℝ) + m₁) := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb : (0 : ℝ) < orb a b i := by exact_mod_cast orb_pos_of_lt (by omega : i < P a b)
  have hz : hm a b i 0 = orb a b i / a := hm_zero hba (P a b - 1 - i) i (by omega)
  have h₀ : 0 < hm a b i 0 := by rw [hz]; positivity
  obtain ⟨h1, h2⟩ := orbit_moment_normalizations hba hi
  have hv := orbit_moment_variance hba hi
  dsimp only
  refine ⟨normalized_first_ne_one h₀ hv h1 h2,
    quotient_from_normalized_moments h₀ hv h1 h2, ?_⟩
  have he : (qq a b i : ℝ) + hm a b i 1 / hm a b i 0 = 1 / hm a b i 0 := by
    apply (eq_div_iff h₀.ne').mpr
    field_simp
    exact h1
  rw [he, one_div, div_inv_eq_mul, hz]
  field_simp

end PierceLengthBound.FixedDividend
