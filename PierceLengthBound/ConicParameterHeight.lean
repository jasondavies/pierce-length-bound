/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicArithmetic
public import Mathlib.Algebra.Polynomial.Degree.Operations

/-! Integer parameters and explicit common-denominator height bounds for a
parabolic conic contained in a bounded integer plane. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial
noncomputable section

/-- A quadratic numerator, with all coefficients represented by integers. -/
def quadraticNumerator (a b c : ℤ) : ℤ[X] := C a + C b * X + C c * X ^ 2

lemma quadraticNumerator_degree (a b c : ℤ) :
    (quadraticNumerator a b c).natDegree ≤ 2 := by
  apply natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by simp) ?_) ?_
  · exact (natDegree_mul_le ..).trans (by simp)
  · exact (natDegree_mul_le ..).trans (by simp)

lemma quadraticNumerator_coeff_bound {a b c M : ℤ} (hM : 0 ≤ M)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ M) :
    ∀ n, |(quadraticNumerator a b c).coeff n| ≤ M := by
  intro n
  rcases n with _ | _ | _ | n
  · simpa [quadraticNumerator] using ha
  · simpa only [quadraticNumerator, coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow,
      coeff_C, Nat.reduceEqDiff, Nat.one_ne_zero, ite_false, ite_true, zero_add, add_zero] using hb
  · norm_num only [quadraticNumerator, coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow,
      coeff_C, Nat.reduceAdd, Nat.reduceEqDiff, ite_false, ite_true, zero_add, add_zero]
    exact hc
  · have hn : 2 < n + 3 := by omega
    rw [coeff_eq_zero_of_natDegree_lt ((quadraticNumerator_degree a b c).trans_lt hn), abs_zero]
    exact hM

lemma quadraticNumerator_eval (a b c t : ℤ) :
    (quadraticNumerator a b c).eval t = a + b * t + c * t ^ 2 := by
  simp [quadraticNumerator]

set_option maxHeartbeats 1000000 in
-- Expanding the three numerators and proving their coefficient bounds is substantial.
/-- The discriminant-zero conic in an integer plane has an injective integer
parameter and quadratic integer numerators with a common nonzero denominator.
The explicit height `33 L K³` bounds all numerator coefficients, and `12 L K³`
bounds the denominator. -/
theorem parabola_integer_parameter_height
    {α β γ d e f ℓ μ ν c : ℤ} {K L : ℕ}
    (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hα : α ≠ 0) (hℓ : ℓ ≠ 0)
    (hJ : 2 * β * d - 4 * α * e ≠ 0) (hΔ : β ^ 2 - 4 * α * γ = 0)
    (hαb : |α| ≤ K) (hβb : |β| ≤ K) (hdb : |d| ≤ K)
    (heb : |e| ≤ K) (hfb : |f| ≤ K)
    (hℓb : |ℓ| ≤ L) (hμb : |μ| ≤ L) (hνb : |ν| ≤ L) (hcb : |c| ≤ L) :
    ∃ (D : ℤ) (N : Fin 3 → ℤ[X]), D ≠ 0 ∧ |D| ≤ 12 * (L : ℤ) * K ^ 3 ∧
      (∀ j, (N j).natDegree ≤ 2) ∧
      (∀ j n, |(N j).coeff n| ≤ 33 * (L : ℤ) * K ^ 3) ∧
      (N 1).coeff 2 ≠ 0 ∧
      (∀ z : Fin 3 → ℤ, conicValue α β γ d e f (z 0) (z 1) = 0 →
        ℓ * z 2 + μ * z 0 + ν * z 1 + c = 0 →
        ∀ j, D * z j = (N j).eval (2 * α * z 0 + β * z 1 + d)) ∧
      Set.InjOn (fun z : Fin 3 → ℤ => 2 * α * z 0 + β * z 1 + d)
        {z | conicValue α β γ d e f (z 0) (z 1) = 0 ∧
          ℓ * z 2 + μ * z 0 + ν * z 1 + c = 0} := by
  let J := 2 * β * d - 4 * α * e
  let E := d ^ 2 - 4 * α * f
  let D := 2 * α * J * ℓ
  let A := β * E - d * J
  let N : Fin 3 → ℤ[X] := ![
    quadraticNumerator (ℓ * A) (ℓ * J) (-ℓ * β),
    quadraticNumerator (-2 * α * ℓ * E) 0 (2 * α * ℓ),
    quadraticNumerator (-μ * A + 2 * ν * α * E - 2 * c * α * J)
      (-μ * J) (μ * β - 2 * ν * α)]
  have hKz : (1 : ℤ) ≤ K := by exact_mod_cast hK
  have hLz : (1 : ℤ) ≤ L := by exact_mod_cast hL
  have mul_bound {x y : ℤ} {B C : ℤ} (hx : |x| ≤ B) (hy : |y| ≤ C) :
      |x * y| ≤ B * C := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)
  have hJE : |J| ≤ 6 * (K : ℤ) ^ 2 ∧ |E| ≤ 5 * (K : ℤ) ^ 2 := by
    have hj := abs_sub_le (2 * β * d) 0 (4 * α * e)
    have he := abs_sub_le (d ^ 2) 0 (4 * α * f)
    simp only [sub_zero, zero_sub, abs_neg, abs_mul, abs_pow] at hj he
    norm_num at hj he
    have hbd := mul_bound hβb hdb
    have hae := mul_bound hαb heb
    have haf := mul_bound hαb hfb
    have hdd := mul_bound hdb hdb
    simp only [abs_mul] at hbd hae haf hdd
    dsimp [J, E]
    constructor
    · nlinarith only [hj, hbd, hae]
    · nlinarith only [he, haf, hdd, sq_abs d]
  have hA : |A| ≤ 11 * (K : ℤ) ^ 3 := by
    have ht := abs_sub_le (β * E) 0 (d * J)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    dsimp [A]
    nlinarith [mul_bound hβb hJE.2, mul_bound hdb hJE.1]
  have hD0 : D ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hα) hJ) hℓ
  have hDb : |D| ≤ 12 * (L : ℤ) * K ^ 3 := by
    have h := mul_bound (mul_bound hαb hJE.1) hℓb
    dsimp [D]
    calc |2 * α * J * ℓ| = 2 * |(α * J) * ℓ| := by
          rw [show 2 * α * J * ℓ = 2 * ((α * J) * ℓ) by ring, abs_mul]
          norm_num
      _ ≤ 2 * ((K : ℤ) * (6 * K ^ 2) * L) := by gcongr
      _ = _ := by ring
  have hcoef : ∀ j n, |(N j).coeff n| ≤ 33 * (L : ℤ) * K ^ 3 := by
    intro j
    have hx0 := mul_bound hℓb hA
    have hx1 := mul_bound hℓb hJE.1
    have hx2 := mul_bound hℓb hβb
    have hy0 := mul_bound (mul_bound hαb hℓb) hJE.2
    have hy2 := mul_bound hαb hℓb
    have hz00 := mul_bound hμb hA
    have hz01 := mul_bound (mul_bound hνb hαb) hJE.2
    have hz02 := mul_bound (mul_bound hcb hαb) hJE.1
    have hz1 := mul_bound hμb hJE.1
    have hz20 := mul_bound hμb hβb
    have hz21 := mul_bound hνb hαb
    have hpow : (K : ℤ) ≤ (K : ℤ) ^ 3 := by nlinarith [sq_nonneg ((K : ℤ) - 1)]
    have hpow2 : (K : ℤ) ^ 2 ≤ (K : ℤ) ^ 3 := by nlinarith [sq_nonneg ((K : ℤ) - 1)]
    have h0 : 0 ≤ 33 * (L : ℤ) * K ^ 3 := by positivity
    have hp1 := mul_le_mul_of_nonneg_left hpow (show (0 : ℤ) ≤ L by omega)
    have hp2 := mul_le_mul_of_nonneg_left hpow2 (show (0 : ℤ) ≤ L by omega)
    simp only [abs_mul] at hx0 hx1 hx2 hy0 hy2 hz00 hz01 hz02 hz1 hz20 hz21
    fin_cases j <;> dsimp [N] <;> apply quadraticNumerator_coeff_bound h0
    · simp only [abs_mul]
      nlinarith only [hx0, h0]
    · simp only [abs_mul]
      nlinarith only [hx1, hp2, h0]
    · simp only [abs_mul, abs_neg]
      nlinarith only [hx2, hp1, h0]
    · norm_num only [abs_mul, abs_neg]
      nlinarith only [hy0, h0]
    · simpa only [abs_zero] using h0
    · norm_num only [abs_mul]
      nlinarith only [hy2, hp1, h0]
    · have ht := abs_sub_le (-μ * A + 2 * ν * α * E) 0 (2 * c * α * J)
      have ht' := abs_add_le (-μ * A) (2 * ν * α * E)
      norm_num only [sub_zero, zero_sub, abs_neg, abs_mul] at ht ht'
      nlinarith only [ht, ht', hz00, hz01, hz02]
    · simp only [abs_mul, abs_neg]
      nlinarith only [hz1, hp2, h0]
    · have ht := abs_sub_le (μ * β) 0 (2 * ν * α)
      norm_num only [sub_zero, zero_sub, abs_neg, abs_mul] at ht
      nlinarith only [ht, hz20, hz21, hp1, h0]
  have heval (z : Fin 3 → ℤ) (hc : conicValue α β γ d e f (z 0) (z 1) = 0)
      (hp : ℓ * z 2 + μ * z 0 + ν * z 1 + c = 0) :
      ∀ j, D * z j = (N j).eval (2 * α * z 0 + β * z 1 + d) := by
    have ht' := parabola_parameter_identity α β γ d e f (z 0) (z 1) hΔ hc
    have ht : (2 * α * z 0 + β * z 1 + d) ^ 2 = J * z 1 + E := by
      dsimp [J, E]
      linear_combination ht'
    intro j
    fin_cases j <;> dsimp [N] <;> rw [quadraticNumerator_eval] <;> dsimp [D, A]
    · linear_combination ℓ * β * ht
    · linear_combination -2 * α * ℓ * ht
    · linear_combination 2 * α * J * hp - (μ * β - 2 * ν * α) * ht
  refine ⟨D, N, hD0, hDb, ?_, hcoef, ?_, heval, ?_⟩
  · intro j
    fin_cases j <;> exact quadraticNumerator_degree _ _ _
  · change (quadraticNumerator (-2 * α * ℓ * E) 0 (2 * α * ℓ)).coeff 2 ≠ 0
    norm_num only [quadraticNumerator, coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow,
      coeff_C, Nat.reduceEqDiff, ite_false, ite_true, zero_add, add_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℤ) ≠ 0) hα) hℓ
  · intro z hz w hw he
    dsimp only at he
    funext j
    apply mul_left_cancel₀ hD0
    rw [heval z hz.1 hz.2 j, heval w hw.1 hw.2 j, he]

/-- The actual integer parameter stays in a polynomially bounded interval. -/
theorem parabola_parameter_abs_le {α β d x y : ℤ} {K H : ℕ} (hH : 1 ≤ H)
    (hα : |α| ≤ K) (hβ : |β| ≤ K) (hd : |d| ≤ K) (hx : |x| ≤ H) (hy : |y| ≤ H) :
    |2 * α * x + β * y + d| ≤ 4 * (K : ℤ) * H := by
  have ht := abs_add_le (2 * α * x + β * y) d
  have ht' := abs_add_le (2 * α * x) (β * y)
  have hx' := mul_le_mul hα hx (abs_nonneg _) (show (0 : ℤ) ≤ K from Nat.cast_nonneg K)
  have hy' := mul_le_mul hβ hy (abs_nonneg _) (show (0 : ℤ) ≤ K from Nat.cast_nonneg K)
  have hHz : (1 : ℤ) ≤ H := by exact_mod_cast hH
  simp only [abs_mul] at ht'
  norm_num at ht'
  nlinarith only [ht, ht', hx', hy', hd, hHz, show (0 : ℤ) ≤ K from Nat.cast_nonneg K]

end
end PierceLengthBound.FixedDividend
