module

public import AffineCurveCounting.LocalDeterminant
public import AffineCurveCounting.PrimeProduct

/-!
# Aggregating the local determinant exponents for curves

Cauchy–Schwarz preserves the leading quadratic coefficient when residue classes
have different multiplicities. These are the numerical aggregation steps in the
curve case of CCDN Proposition 2.6. The geometric local divisibility and finite
field multiplicity estimates remain separate proof obligations.
-/

@[expose] public section
namespace AffineCurveCounting
open Finset

/-- Aggregate classwise quadratic estimates without losing the leading constant. -/
theorem aggregate_local_exponents {ι : Type*} (S : Finset ι)
    (n μ e : ι → ℕ) (he : ∀ i ∈ S, n i ^ 2 ≤ 2 * μ i * (e i + n i)) :
    (∑ i ∈ S, n i) ^ 2 ≤ 2 * (∑ i ∈ S, μ i) * ((∑ i ∈ S, e i) + ∑ i ∈ S, n i) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (r := n) (f := fun i => 2 * μ i) (g := fun i => e i + n i)
    (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _) he
  simpa only [← mul_sum, sum_add_distrib, mul_assoc] using h

/-- Apply the aggregation directly to the repeated local weights. -/
theorem aggregate_multiplicity_exponents {ι : Type*} (S : Finset ι)
    (n μ : ι → ℕ) (hμ : ∀ i ∈ S, 0 < μ i) :
    (∑ i ∈ S, n i) ^ 2 ≤ 2 * (∑ i ∈ S, μ i) *
      ((∑ i ∈ S, multiplicityExponent (n i) (μ i)) + ∑ i ∈ S, n i) :=
  aggregate_local_exponents S n μ _ (fun i hi => multiplicityExponent_lower_bound _ _ (hμ i hi))

/-- Real-valued form with a uniform upper bound for total residue multiplicity. -/
theorem aggregate_exponent_lower {ι : Type*} (S : Finset ι)
    (n μ e : ι → ℕ) (he : ∀ i ∈ S, n i ^ 2 ≤ 2 * μ i * (e i + n i))
    {N : ℝ} (hN : 0 < N) (hμ : (∑ i ∈ S, μ i : ℕ) ≤ N) :
    (∑ i ∈ S, n i : ℕ) ^ 2 / (2 * N) - (∑ i ∈ S, n i : ℕ) ≤
      (∑ i ∈ S, e i : ℕ) := by
  have h : ((∑ i ∈ S, n i : ℕ) : ℝ) ^ 2 ≤
      2 * ((∑ i ∈ S, μ i : ℕ) : ℝ) *
        (((∑ i ∈ S, e i : ℕ) : ℝ) + (∑ i ∈ S, n i : ℕ)) := by
    exact_mod_cast aggregate_local_exponents S n μ e he
  apply sub_le_iff_le_add.mpr
  apply (div_le_iff₀ (by positivity : 0 < 2 * N)).mpr
  calc _ ≤ 2 * ((∑ i ∈ S, μ i : ℕ) : ℝ) *
        (((∑ i ∈ S, e i : ℕ) : ℝ) + (∑ i ∈ S, n i : ℕ)) := h
    _ ≤ _ := by nlinarith

/-- Local multiplicity bounds and prime-power divisibility give the global log
lower bound. Neither the local divisibility nor the prime sums are assumed solved. -/
theorem log_lower_of_local_exponents (P : Finset ℕ) (e : ℕ → ℕ)
    (N : ℕ → ℝ) (s : ℕ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, Nat.Prime p) (hN : ∀ p ∈ P, 0 < N p)
    (he : ∀ p ∈ P, (s : ℝ) ^ 2 / (2 * N p) - s ≤ e p)
    (hdiv : ∀ p ∈ P, (p : ℤ) ^ e p ∣ D) :
    (s : ℝ) ^ 2 / 2 * (∑ p ∈ P, Real.log p / N p) -
      s * (∑ p ∈ P, Real.log p) ≤ Real.log D := by
  have hsum : ∑ p ∈ P, (((s : ℝ) ^ 2 / (2 * N p) - s) * Real.log p) ≤
      ∑ p ∈ P, (e p : ℝ) * Real.log p := by
    apply sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_right (he p hp)
      (Real.log_nonneg (by exact_mod_cast (hP p hp).one_lt.le))
  have heq : (∑ p ∈ P, (((s : ℝ) ^ 2 / (2 * N p) - s) * Real.log p)) =
      (s : ℝ) ^ 2 / 2 * (∑ p ∈ P, Real.log p / N p) -
        s * (∑ p ∈ P, Real.log p) := by
    simp only [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    field_simp [(hN p hp).ne']
  rw [heq] at hsum
  exact hsum.trans (sum_log_prime_powers_le_log P e hD hP hdiv)

end AffineCurveCounting
