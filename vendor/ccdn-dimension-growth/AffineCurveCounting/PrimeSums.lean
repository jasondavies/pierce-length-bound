module

public import AffineCurveCounting.MertensFirst
public import AffineCurveCounting.ResidueAggregation

/-! Prime-sum estimates after excluding a finite bad-prime set. The bounds on
finite-field multiplicities and the bad-prime set remain geometric obligations. -/

@[expose] public section
namespace AffineCurveCounting
open Finset Real

noncomputable def mertensError : ℝ := Real.log 4 + 6 + Mertens.E₁

lemma mertensError_pos : 0 < mertensError := by
  have hE : 0 ≤ Mertens.E₁ := tsum_nonneg Mertens.E₁.summand_nonneg
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold mertensError
  linarith

/-- The first Mertens estimate retains an explicit charge for excluded primes. -/
theorem prime_sum_lower_sdiff {x : ℝ} (hx : 1 ≤ x) (B : Finset ℕ) :
    Real.log x - mertensError - (∑ p ∈ B, Real.log p / p) ≤
      ∑ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, Real.log p / p := by
  let S := (Ioc 0 ⌊x⌋₊).filter Nat.Prime
  have hm := (abs_le.mp (Mertens.prime_sum_bounded_error hx)).1
  have he := sum_inter_add_sum_sdiff S B (fun p : ℕ => Real.log p / p)
  have hB : (∑ p ∈ S ∩ B, Real.log p / p) ≤ ∑ p ∈ B, Real.log p / p := by
    apply sum_le_sum_of_subset_of_nonneg inter_subset_right
    intro p _ _
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  change Real.log x - mertensError - _ ≤ ∑ p ∈ S \ B, Real.log p / p
  change -mertensError ≤ (∑ p ∈ S, Real.log p / p) - Real.log x at hm
  linarith

/-- A summable majorant for the error caused by a square-root point-count term. -/
lemma summable_prime_error_majorant : Summable (fun n : ℕ => 4 / (n : ℝ) ^ (5 / 4 : ℝ)) :=
  (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 5 / 4)).const_div 4

noncomputable def primeErrorMass : ℝ := ∑' n : ℕ, 4 / (n : ℝ) ^ (5 / 4 : ℝ)

/-- A square-root perturbation of `p` has a summable weighted reciprocal error. -/
lemma log_div_sqrt_perturbation {p C N : ℝ} (hp : 1 ≤ p) (hC : 0 ≤ C)
    (hN : 0 < N) (hupper : N ≤ p + C * Real.sqrt p) :
    Real.log p / p - C * (4 / p ^ (5 / 4 : ℝ)) ≤ Real.log p / N := by
  have hp0 : 0 < p := by linarith
  have hl : 0 ≤ Real.log p := Real.log_nonneg hp
  have hs : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hpC : 0 < p + C * Real.sqrt p := by positivity
  have hrec : 1 / p - C * Real.sqrt p / p ^ 2 ≤ 1 / (p + C * Real.sqrt p) := by
    field_simp
    nlinarith [sq_nonneg C, Real.sq_sqrt hp0.le]
  have hlog : Real.log p * (Real.sqrt p / p ^ 2) ≤ 4 / p ^ (5 / 4 : ℝ) := by
    have hb := Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 4)
    calc Real.log p * (Real.sqrt p / p ^ 2) ≤
          (p ^ (1 / 4 : ℝ) / (1 / 4 : ℝ)) * (Real.sqrt p / p ^ 2) := by gcongr
      _ = 4 / p ^ (5 / 4 : ℝ) := by
        have he : p ^ (1 / 4 : ℝ) * Real.sqrt p * p ^ (5 / 4 : ℝ) = p ^ 2 := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
          norm_num
        field_simp
        nlinarith [he]
  calc Real.log p / p - C * (4 / p ^ (5 / 4 : ℝ)) ≤
      Real.log p * (1 / p - C * Real.sqrt p / p ^ 2) := by
        calc _ ≤ Real.log p / p - C * (Real.log p * (Real.sqrt p / p ^ 2)) :=
              sub_le_sub_left (mul_le_mul_of_nonneg_left hlog hC) _
          _ = _ := by ring
    _ ≤ Real.log p * (1 / (p + C * Real.sqrt p)) := mul_le_mul_of_nonneg_left hrec hl
    _ ≤ Real.log p / N := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_left hl hN hupper

/-- The analytic part of the weighted good-prime sum; constants are independent of
coefficients. Curve-specific bounds for `N` and the excluded set are explicit. -/
theorem weighted_prime_sum_lower {x C : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C)
    (B : Finset ℕ) (N : ℕ → ℝ)
    (hN : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, 0 < N p)
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B,
      N p ≤ p + C * Real.sqrt p) :
    Real.log x - mertensError - (∑ p ∈ B, Real.log p / p) - C * primeErrorMass ≤
      ∑ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, Real.log p / N p := by
  let S := ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B
  have hpoint : ∀ p ∈ S,
      Real.log p / p - C * (4 / (p : ℝ) ^ (5 / 4 : ℝ)) ≤ Real.log p / N p := by
    intro p hp
    have hprime := (mem_filter.mp (mem_sdiff.mp hp).1).2
    exact log_div_sqrt_perturbation (by exact_mod_cast hprime.one_le) hC
      (hN p hp) (hupper p hp)
  have hs := sum_le_sum hpoint
  rw [sum_sub_distrib, ← mul_sum] at hs
  have ht : (∑ p ∈ S, 4 / (p : ℝ) ^ (5 / 4 : ℝ)) ≤ primeErrorMass :=
    summable_prime_error_majorant.sum_le_tsum S (fun _ _ => by positivity)
  have hm := prime_sum_lower_sdiff hx B
  change Real.log x - mertensError - _ ≤ ∑ p ∈ S, Real.log p / p at hm
  change _ ≤ ∑ p ∈ S, Real.log p / N p
  nlinarith

/-- A product controlling the excluded primes controls their weighted logarithms. -/
theorem bad_prime_charge_le {D : ℤ} (hD : 0 < D) (B : Finset ℕ)
    (hprime : ∀ p ∈ B, Nat.Prime p) (hdiv : ∀ p ∈ B, (p : ℤ) ∣ D)
    {L : ℝ} (hL : 0 < L) (hlarge : ∀ p ∈ B, L ≤ p) :
    (∑ p ∈ B, Real.log p / p) ≤ Real.log D / L := by
  have hb := sum_log_prime_powers_le_log B (fun _ => 1) hD hprime
    (fun p hp => by simpa using hdiv p hp)
  simp only [Nat.cast_one, one_mul] at hb
  calc
    (∑ p ∈ B, Real.log p / p) ≤ ∑ p ∈ B, Real.log p / L := by
      apply sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) hL (hlarge p hp)
    _ = (∑ p ∈ B, Real.log p) / L := (sum_div _ _ _).symm
    _ ≤ Real.log D / L := div_le_div_of_nonneg_right hb hL.le

/-- Analytic determinant lower bound from explicit local geometric inputs.
This proves the prime-sum step; the geometric inputs are not asserted here. -/
theorem determinant_log_lower_from_local_bounds {x C : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C)
    (B : Finset ℕ) (N : ℕ → ℝ) (s : ℕ) (e : ℕ → ℕ) {D : ℤ} (hD : 0 < D)
    (hN : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, 0 < N p)
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B,
      N p ≤ p + C * Real.sqrt p)
    (he : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B,
      (s : ℝ) ^ 2 / (2 * N p) - s ≤ e p)
    (hdiv : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, (p : ℤ) ^ e p ∣ D) :
    (s : ℝ) ^ 2 / 2 * (Real.log x - mertensError -
      (∑ p ∈ B, Real.log p / p) - C * primeErrorMass) -
      s * ((Real.log 4 + 4) * x) ≤ Real.log D := by
  let S := ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B
  have hp : ∀ p ∈ S, Nat.Prime p := fun p hp => (mem_filter.mp (mem_sdiff.mp hp).1).2
  have hbase := log_lower_of_local_exponents S e N s hD hp hN he hdiv
  have hm := weighted_prime_sum_lower hx hC B N hN hupper
  have htheta : (∑ p ∈ S, Real.log p) ≤ (Real.log 4 + 4) * x := by
    calc
      (∑ p ∈ S, Real.log p) ≤ Chebyshev.theta x := by
        apply sum_le_sum_of_subset_of_nonneg sdiff_subset
        intro p _ _
        exact Real.log_natCast_nonneg p
      _ ≤ Chebyshev.psi x := Chebyshev.theta_le_psi x
      _ ≤ _ := Chebyshev.psi_le_const_mul_self (by linarith)
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity)
  have ht' := mul_le_mul_of_nonneg_left htheta (show (0 : ℝ) ≤ s by positivity)
  linarith

end AffineCurveCounting
