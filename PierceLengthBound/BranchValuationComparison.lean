/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralBranchOrders

/-! Comparing a centered discrete order with the canonical order of its Dedekind branch. An
integer-valued order of the fraction field that attains `1`, is nonnegative on a Dedekind domain
`R` and is positive exactly on the prime `p` equals `normalizedBranchOrder p`, since the
valuation ring determines a normalized integer order. Consequently normalized branch orders are
injective in `p`, and a branch at which `x` vanishes is a branch of the zero fiber of the
parameter normalization of `x`, with the same order. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- An order nonnegative on `R`, positive exactly on `p` and attaining `1` has the same
valuation ring as the `p`-adic valuation. -/
theorem centered_branch_valuationSubring {R L : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (p : IsDedekindDomain.HeightOneSpectrum R) (ν : AddValuation L (WithTop ℤ))
    (hR : ∀ r : R, 0 ≤ ν (algebraMap R L r))
    (hp : ∀ r : R, r ∈ p.asIdeal ↔ 0 < ν (algebraMap R L r))
    (hπ : ∃ π : L, ν π = 1) :
    (p.valuation L).valuationSubring = ν.toValuation.valuationSubring := by
  have hle : p.valuationSubringAtPrime L ≤ ν.toValuation.valuationSubring := by
    rintro z ⟨a, s, hs, rfl⟩
    change 0 ≤ ν (algebraMap R L a * (algebraMap R L s)⁻¹)
    rw [← div_eq_mul_inv]
    have hs' : s ∉ p.asIdeal := hs
    have hs0 : ν (algebraMap R L s) = 0 :=
      le_antisymm (le_of_not_gt (fun h => hs' ((hp s).mpr h))) (hR s)
    rw [ν.map_div, hs0, sub_zero]
    exact hR a
  have htop : ν.toValuation.valuationSubring ≠ ⊤ := by
    intro h
    obtain ⟨π, hπ⟩ := hπ
    have hm : π⁻¹ ∈ ν.toValuation.valuationSubring := by rw [h]; trivial
    change 0 ≤ ν π⁻¹ at hm
    rw [ν.map_inv, hπ] at hm
    change ((0 : ℤ) : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) at hm
    norm_num only [WithTop.coe_le_coe] at hm
  rw [← p.valuationSubringAtPrime_eq_valuationSubring]
  exact ValuationSubring.eq_of_le_of_ne_top _ hle htop

/-- `ν (x ^ n) = n · ν x` for integer powers. -/
lemma discrete_order_zpow {L : Type*} [Field L] (ν : AddValuation L (WithTop ℤ))
    {x : L} {m : ℤ} (hx : ν x = (m : WithTop ℤ)) (n : ℤ) :
    ν (x ^ n) = ((n * m : ℤ) : WithTop ℤ) := by
  cases n with
  | ofNat n => simp [ν.map_pow, hx, ← WithTop.coe_nsmul]
  | negSucc n =>
      rw [zpow_negSucc, ν.map_inv, ν.map_pow, hx, ← WithTop.coe_nsmul,
        ← WithTop.LinearOrderedAddCommGroup.coe_neg]
      congr 1
      simp only [Int.negSucc_eq]
      ring

/-- Equivalent integer-valued orders that both attain one are equal. The
normalization excludes a nontrivial positive rescaling of the value group. -/
theorem normalized_discrete_orders_eq {L : Type*} [Field L]
    (ν μ : AddValuation L (WithTop ℤ)) (h : ν.IsEquiv μ)
    (hν : ∃ π : L, ν π = 1) (hμ : ∃ π : L, μ π = 1) : ν = μ := by
  have hle (a b : L) : ν a ≤ ν b ↔ μ a ≤ μ b := h b a
  have hpos (a : L) : 0 < ν a ↔ 0 < μ a := by
    have hh : ν 1 < ν a ↔ μ 1 < μ a := by
      simp only [lt_iff_le_not_ge, hle]
    simpa only [ν.map_one, μ.map_one] using hh
  obtain ⟨π, hπ⟩ := hν
  obtain ⟨κ, hκ⟩ := hμ
  have hπ0 : π ≠ 0 := by intro hz; simp [hz] at hπ
  have hκ0 : κ ≠ 0 := by intro hz; simp [hz] at hκ
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (μ.ne_top_iff.mpr hπ0)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ν.ne_top_iff.mpr hκ0)
  have hmpos : 0 < m := by
    have hh := (hpos π).mp (by rw [hπ]; exact zero_lt_one)
    rw [← hm] at hh
    exact_mod_cast hh
  have hnpos : 0 < n := by
    have hh := (hpos κ).mpr (by rw [hκ]; exact zero_lt_one)
    rw [← hn] at hh
    exact_mod_cast hh
  have he : ν (π ^ n) = ν κ := by
    rw [discrete_order_zpow ν hπ n, mul_one, hn]
  have hnm : n * m = 1 := by
    have hh := h.val_eq.mp he
    rw [discrete_order_zpow μ hm.symm n, hκ] at hh
    exact_mod_cast hh
  have hm1 : m = 1 := by
    have hle : m ≤ n * m := by
      simpa using mul_le_mul_of_nonneg_right (show 1 ≤ n by omega) hmpos.le
    omega
  have hμπ : μ π = 1 := by rw [← hm, hm1]; rfl
  apply AddValuation.ext
  intro x
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (ν.ne_top_iff.mpr hx)
  have he : ν x = ν (π ^ k) := by rw [discrete_order_zpow ν hπ k, mul_one, hk]
  have he' := h.val_eq.mp he
  rw [discrete_order_zpow μ hμπ k, mul_one] at he'
  exact hk.symm.trans he'.symm

theorem normalizedBranchOrder_valuationSubring {R L : Type*} [CommRing R]
    [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    (normalizedBranchOrder p L).toValuation.valuationSubring =
      (p.valuation L).valuationSubring := by
  ext x
  change 0 ≤ discreteNegativeLog (p.valuation L x) ↔ p.valuation L x ≤ 1
  rw [← discreteNegativeLog_one, discreteNegativeLog_le_iff]

/-- A normalized discrete order centered at a Dedekind branch is exactly the
canonical order of that branch, on every function in the fraction field. -/
theorem centered_branch_order_eq {R L : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (p : IsDedekindDomain.HeightOneSpectrum R) (ν : AddValuation L (WithTop ℤ))
    (hR : ∀ r : R, 0 ≤ ν (algebraMap R L r))
    (hp : ∀ r : R, r ∈ p.asIdeal ↔ 0 < ν (algebraMap R L r))
    (hπ : ∃ π : L, ν π = 1) : normalizedBranchOrder p L = ν := by
  apply normalized_discrete_orders_eq _ _ ?_ (normalizedBranchOrder_uniformizer p L) hπ
  change (normalizedBranchOrder p L).toValuation.IsEquiv ν.toValuation
  apply (Valuation.isEquiv_iff_valuationSubring ..).mpr
  rw [normalizedBranchOrder_valuationSubring]
  exact centered_branch_valuationSubring p ν hR hp hπ

/-- Distinct height-one primes have distinct normalized orders. -/
theorem normalizedBranchOrder_injective {R L : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] :
    Function.Injective (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      normalizedBranchOrder p L) := by
  intro p q h
  change normalizedBranchOrder p L = normalizedBranchOrder q L at h
  apply IsDedekindDomain.HeightOneSpectrum.ext
  apply Ideal.ext
  intro r
  rw [← normalizedBranchOrder_positive_iff p L r,
    ← normalizedBranchOrder_positive_iff q L r, h]

/-- An integer-valued order of `L` that is nonnegative on `ℚ`, attains `1` and is positive at
`x` is the canonical order of a branch `q` in the zero fiber of the parameter normalization
of `x`. -/
theorem function_parameter_branch_transport {L : Type*} [Field L] [Algebra ℚ L]
    (ν : AddValuation L (WithTop ℤ)) (hQ : ∀ c : ℚ, 0 ≤ ν (algebraMap ℚ L c))
    (hπ : ∃ π : L, ν π = 1) (x : L) (hx : Transcendental ℚ x)
    [FiniteDimensional (IntermediateField.adjoin ℚ {x}) L] (hpos : 0 < ν x) :
    ∃ q : IsDedekindDomain.HeightOneSpectrum (functionParameterNormalization x),
      functionParameterElement x ∈ q.asIdeal ∧ functionParameterBranchOrder x hx q = ν := by
  let C := functionParameterNormalization x
  let : IsDedekindDomain C := (function_parameter_normalization x hx).1
  let : IsFractionRing C L := (function_parameter_normalization x hx).2.2
  obtain ⟨q, hq, hmem⟩ := function_parameter_center ν hQ hx.ne_zero hpos
  refine ⟨q, hmem, ?_⟩
  apply centered_branch_order_eq q ν ?_ hq hπ
  exact branch_order_nonnegative_on_normalization ν
    (branch_order_nonnegative_on_parameter_algebra ν hQ hpos.le)

end
end PierceLengthBound.FixedDividend
