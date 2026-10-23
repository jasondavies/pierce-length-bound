/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftCofactors
public import PierceLengthBound.FixedDividendIdentity

/-! The eight-row moment system of an orbit state: the coefficient rows of
`Q_i, X Q_i, X² Q_i, X³ Q_i` and of the same shifts of `X · nextQuartic`, which annihilate the
moment vector `(h_i(j))_{j ≤ 8}` and are linearly independent. With `IntegralLiftCofactors` this
gives the cofactor reconstruction `orbitMomentSystem_reconstruction`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Matrix Finset

/-- The shifted polynomials `P Xʲ` and `Z Xʲ` for `j < 4`. -/
def shiftedMomentPolynomial {K : Type*} [CommRing K] (P Z : K[X]) : Fin 4 ⊕ Fin 4 → K[X] :=
  Sum.elim (fun j => P * X ^ j.val) (fun j => Z * X ^ j.val)

/-- For `deg P = 4` and `P` coprime to `Z`, the eight shifted polynomials are linearly
independent. -/
theorem shiftedMomentPolynomial_independent {K : Type*} [Field K]
    (P Z : K[X]) (hP : P.natDegree = 4) (hcop : IsCoprime P Z) :
    LinearIndependent K (shiftedMomentPolynomial P Z) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let U : K[X] := ∑ k : Fin 4, C (c (.inl k)) * X ^ k.val
  let V : K[X] := ∑ k : Fin 4, C (c (.inr k)) * X ^ k.val
  have hv : V.natDegree < P.natDegree := by
    rw [hP]
    have hh : V.natDegree ≤ 3 := by
      apply natDegree_sum_le_of_forall_le
      intro k _
      exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)
    omega
  have hrel : U * P + V * Z = 0 := by
    simpa only [U, V, sum_mul, mul_sum, shiftedMomentPolynomial, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, smul_eq_C_mul, mul_assoc, mul_comm, mul_left_comm] using hc
  obtain ⟨hu, hv⟩ := shifted_quartics_independent
    (ne_zero_of_natDegree_gt (show 0 < P.natDegree by omega)) hcop hv hrel
  rcases j with j | j
  · have h := congrArg (fun f : K[X] => f.coeff j.val) hu
    simpa [U, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using h
  · have h := congrArg (fun f : K[X] => f.coeff j.val) hv
    simpa [V, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using h

def momentSystemPolynomial {K : Type*} [CommRing K] (P Z : K[X]) (j : Fin 8) : K[X] :=
  shiftedMomentPolynomial P Z (finSumFinEquiv.symm j)

/-- The `8 × 9` matrix of coefficients of `t⁰, …, t⁸` of the shifted polynomials. -/
def momentSystem {K : Type*} [CommRing K] (P Z : K[X]) : Matrix (Fin 8) (Fin 9) K :=
  fun i j => (momentSystemPolynomial P Z i).coeff j.val

lemma momentSystemPolynomial_degree {K : Type*} [Field K] (P Z : K[X])
    (hP : P.natDegree ≤ 4) (hZ : Z.natDegree ≤ 5) (i : Fin 8) :
    (momentSystemPolynomial P Z i).natDegree ≤ 8 := by
  unfold momentSystemPolynomial
  rcases (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8).symm i with j | j
  · change (P * X ^ j.val).natDegree ≤ 8
    have h := natDegree_mul_le (p := P) (q := X ^ j.val)
    rw [natDegree_X_pow] at h
    omega
  · change (Z * X ^ j.val).natDegree ≤ 8
    have h := natDegree_mul_le (p := Z) (q := X ^ j.val)
    rw [natDegree_X_pow] at h
    omega

/-- Truncating at coefficient eight loses no information in the eight shifted rows. -/
theorem momentSystem_independent {K : Type*} [Field K] (P Z : K[X])
    (hP : P.natDegree = 4) (hZ : Z.natDegree ≤ 5) (hcop : IsCoprime P Z) :
    LinearIndependent K (momentSystem P Z).row := by
  have hi : LinearIndependent K (momentSystemPolynomial P Z) :=
    (shiftedMomentPolynomial_independent P Z hP hcop).comp
      finSumFinEquiv.symm finSumFinEquiv.symm.injective
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  apply Fintype.linearIndependent_iff.mp hi c _ j
  ext k
  by_cases hk : k < 9
  · have h := congrFun hc (⟨k, hk⟩ : Fin 9)
    simpa only [finsetSum_coeff, coeff_smul, coeff_zero, Pi.zero_apply, Finset.sum_apply,
      Pi.smul_apply, Matrix.row, momentSystem] using h
  · have hd : (∑ i : Fin 8, c i • momentSystemPolynomial P Z i).natDegree ≤ 8 := by
      apply natDegree_sum_le_of_forall_le
      intro i _
      exact (natDegree_smul_le _ _).trans (momentSystemPolynomial_degree P Z hP.le hZ i)
    rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_zero]

lemma orbitShiftedQuintic_degree (a b i : ℕ) :
    (X * nextQuartic a b i).natDegree = 5 := by
  rw [natDegree_mul monic_X.ne_zero (nextQuartic_monic i).ne_zero,
    natDegree_X, nextQuartic_natDegree]

/-- The orbit quartic is coprime to `X · nextQuartic`: a common root would make their
resultant vanish, contradicting `orbit_fixed_dividend_identity` and the positivity of the
orbit norm. -/
theorem orbitQuartic_coprime_shifted {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    IsCoprime (orbitQuartic a b i) (X * nextQuartic a b i) := by
  by_contra h
  have hr := resultant_eq_zero_iff.mpr ⟨Or.inl (orbitQuartic_monic i).ne_zero, h⟩
  rw [orbitQuartic_natDegree, orbitShiftedQuintic_degree] at hr
  have he := orbit_fixed_dividend_identity hba hi
  rw [hr, mul_zero] at he
  have ha : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hd := orbitNorm_pos hba hi
  have : 0 < (a : ℝ) * orbitNorm a b i ^ 4 := by positivity
  linarith

/-- The moment system of the orbit state `i`. -/
def orbitMomentSystem (a b i : ℕ) : Matrix (Fin 8) (Fin 9) ℝ :=
  momentSystem (orbitQuartic a b i) (X * nextQuartic a b i)

theorem orbitMomentSystem_independent {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    LinearIndependent ℝ (orbitMomentSystem a b i).row :=
  momentSystem_independent _ _ (orbitQuartic_natDegree i)
    (orbitShiftedQuintic_degree a b i).le (orbitQuartic_coprime_shifted hba hi)

/-- `ν_i(f) = ∑_{j ≤ 8} [Xʲ]f · h_i(j)` for `deg f ≤ 8`. -/
lemma nuF_eq_sum_nine {a b i : ℕ} (f : ℝ[X]) (hf : f.natDegree ≤ 8) :
    nuF a b i f = ∑ j : Fin 9, f.coeff j.val * hm a b i j.val := by
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow' (show f.natDegree < 9 by omega)]
  rw [nuF_sum]
  simp only [nuF_C_mul, nuF_X_pow]
  exact (Fin.sum_univ_eq_sum_range (fun k => f.coeff k * hm a b i k) 9).symm

/-- The moment vector `(h_i(j))_{j ≤ 8}` lies in the kernel of the orbit moment system. -/
theorem orbitMomentSystem_kernel {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    orbitMomentSystem a b i *ᵥ (fun j => hm a b i j.val) = 0 := by
  ext k
  change (∑ j : Fin 9,
    (momentSystemPolynomial (orbitQuartic a b i) (X * nextQuartic a b i) k).coeff j.val *
      hm a b i j.val) = 0
  rw [← nuF_eq_sum_nine _ (momentSystemPolynomial_degree _ _
    (orbitQuartic_natDegree i).le (orbitShiftedQuintic_degree a b i).le k)]
  unfold momentSystemPolynomial
  rcases (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8).symm k with j | j
  · exact orbitQuartic_orthogonal hba (by omega) j.val j.isLt
  · exact nextQuartic_orthogonal hba hi j.val j.isLt

/-- Cofactor reconstruction at every orbit state with `i + 7 < P(a,b)`, from the orbit moment
system: `c₀ ≠ 0`, `q_i = (c₁ - c₂) / (c₁ - c₀)` and
`h_i(j) = c_j (c₁ - c₀) / (c₁² - c₀ c₂)`. -/
theorem orbitMomentSystem_reconstruction {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    let c := momentCofactors (orbitMomentSystem a b i)
    c 0 ≠ 0 ∧ c 1 - c 0 ≠ 0 ∧ c 1 ^ 2 - c 0 * c 2 ≠ 0 ∧
      (qq a b i : ℝ) = (c 1 - c 2) / (c 1 - c 0) ∧
      ∀ j : Fin 9, hm a b i j.val =
        c j * (c 1 - c 0) / (c 1 ^ 2 - c 0 * c 2) :=
  orbit_cofactor_reconstruction hba (by omega) (orbitMomentSystem a b i)
    (orbitMomentSystem_independent hba hi) (orbitMomentSystem_kernel hba hi)

end
end PierceLengthBound.FixedDividend
