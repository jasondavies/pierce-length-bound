module

public import AffineCurveCounting.PrimitiveNormalization
public import Mathlib.LinearAlgebra.Lagrange

/-! Explicit coefficient control from values at the integer grid 0,...,d.
This is the quantitative input for positioning a large leading coefficient. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Finset

lemma real_polynomial_linear_mul_bound {f : ℝ[X]} {H : ℝ} (hH : 0 ≤ H)
    (hf : ∀ k, |f.coeff k| ≤ H) (a b : ℝ) (k : ℕ) :
    |((C a * X + C b) * f).coeff k| ≤ (|a| + |b|) * H := by
  rw [add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_C_mul]
  cases k with
  | zero =>
    simp only [coeff_X_mul_zero, mul_zero, zero_add, abs_mul]
    nlinarith [hf 0, abs_nonneg a, abs_nonneg b]
  | succ k =>
    rw [coeff_X_mul]
    have h := abs_add_le (a * f.coeff k) (b * f.coeff (k + 1))
    rw [abs_mul, abs_mul] at h
    have h₁ := mul_le_mul_of_nonneg_left (hf k) (abs_nonneg a)
    have h₂ := mul_le_mul_of_nonneg_left (hf (k + 1)) (abs_nonneg b)
    nlinarith

lemma nat_cast_sub_abs_one_le {i j : ℕ} (hij : i ≠ j) : (1 : ℝ) ≤ |(i : ℝ) - j| := by
  have h : (i : ℤ) - j ≠ 0 := by exact sub_ne_zero.mpr (by exact_mod_cast hij)
  have hh := Int.one_le_abs h
  exact_mod_cast hh

lemma lagrange_integer_factor_mul_bound {d i j : ℕ} (hj : j ≤ d) (hij : i ≠ j)
    {f : ℝ[X]} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ k, |f.coeff k| ≤ H) (k : ℕ) :
    |(Lagrange.basisDivisor (i : ℝ) (j : ℝ) * f).coeff k| ≤ ((d : ℝ) + 1) * H := by
  have hab := nat_cast_sub_abs_one_le hij
  have hinv : |((i : ℝ) - j)⁻¹| ≤ 1 := by
    rw [abs_inv]
    exact inv_le_one_of_one_le₀ hab
  have hjR : (j : ℝ) ≤ d := by exact_mod_cast hj
  have he : Lagrange.basisDivisor (i : ℝ) (j : ℝ) =
      C (((i : ℝ) - j)⁻¹) * X + C (-((i : ℝ) - j)⁻¹ * j) := by
    simp only [Lagrange.basisDivisor, neg_mul, map_neg, map_mul, sub_eq_add_neg]
    ring
  rw [he]
  have hh := real_polynomial_linear_mul_bound hH hf (((i : ℝ) - j)⁻¹)
    (-((i : ℝ) - j)⁻¹ * j) k
  have hc : |((i : ℝ) - j)⁻¹| + |-((i : ℝ) - j)⁻¹ * j| ≤ (d : ℝ) + 1 := by
    rw [abs_mul, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ j by positivity)]
    nlinarith [abs_nonneg (((i : ℝ) - j)⁻¹)]
  exact hh.trans (mul_le_mul_of_nonneg_right hc hH)

lemma lagrange_integer_product_coefficient_bound {d i : ℕ} (s : Finset ℕ)
    (hs : ∀ j ∈ s, j ≤ d ∧ i ≠ j) (k : ℕ) :
    |(∏ j ∈ s, Lagrange.basisDivisor (i : ℝ) (j : ℝ)).coeff k| ≤ ((d : ℝ) + 1) ^ s.card := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    by_cases hk : k = 0 <;> simp [coeff_one, hk]
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj, pow_succ]
    have hj' := hs j (mem_insert_self _ _)
    have hh : ∀ k, |(∏ l ∈ s, Lagrange.basisDivisor (i : ℝ) (l : ℝ)).coeff k| ≤
        ((d : ℝ) + 1) ^ s.card := fun k => ih (fun l hl => hs l (mem_insert_of_mem hl)) k
    simpa only [mul_comm] using lagrange_integer_factor_mul_bound hj'.1 hj'.2
      (by positivity) hh k

lemma lagrange_integer_basis_coefficient_bound {d i : ℕ} (hi : i ≤ d) (k : ℕ) :
    |(Lagrange.basis (range (d + 1)) (fun j : ℕ => (j : ℝ)) i).coeff k| ≤ ((d : ℝ) + 1) ^ d := by
  have hi' : i ∈ range (d + 1) := mem_range.mpr (by omega)
  have h := lagrange_integer_product_coefficient_bound (d := d) (i := i) ((range (d + 1)).erase i)
    (fun j hj => ⟨by have := (mem_erase.mp hj).2; simp only [mem_range] at this; omega,
      (mem_erase.mp hj).1.symm⟩) k
  simpa only [Lagrange.basis, card_erase_of_mem hi', card_range, Nat.add_sub_cancel] using h

/-- All coefficients are controlled by the values on 0,...,d, with an
explicit factor small enough for an exp(O(d²)) coordinate-position loss. -/
theorem polynomial_coefficient_bound_of_integer_grid (f : ℝ[X]) {d : ℕ} (hd : f.natDegree ≤ d)
    {H : ℝ} (hH : 0 ≤ H) (heval : ∀ i : ℕ, i ≤ d → |f.eval (i : ℝ)| ≤ H) (k : ℕ) :
    |f.coeff k| ≤ ((d : ℝ) + 1) ^ (d + 1) * H := by
  have hinj : Set.InjOn (fun i : ℕ => (i : ℝ)) (range (d + 1)) :=
    Nat.cast_injective.injOn
  have hdeg : f.degree < (range (d + 1)).card := by
    rw [card_range, degree_lt_iff_coeff_zero]
    intro n hn
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  have he := Lagrange.eq_interpolate hinj hdeg
  conv_lhs => rw [he]
  rw [Lagrange.interpolate_apply, finsetSum_coeff]
  calc
    _ ≤ ∑ i ∈ range (d + 1), |(C (f.eval (i : ℝ)) *
        Lagrange.basis (range (d + 1)) (fun j : ℕ => (j : ℝ)) i).coeff k| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range (d + 1), H * ((d : ℝ) + 1) ^ d := by
      apply sum_le_sum
      intro i hi
      have hi' : i ≤ d := by have := mem_range.mp hi; omega
      rw [coeff_C_mul, abs_mul]
      exact mul_le_mul (heval i hi') (lagrange_integer_basis_coefficient_bound hi' k)
        (abs_nonneg _) hH
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, pow_succ]; ring

end
end AffineCurveCounting
