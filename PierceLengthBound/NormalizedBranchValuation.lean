/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-! Integer-valued additive orders on normalized branches, obtained from the
canonical adic valuations at height-one primes of a Dedekind normalization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Negative logarithm, sending the multiplicative zero to additive infinity. -/
def discreteNegativeLog (x : WithZero (Multiplicative ℤ)) : WithTop ℤ :=
  if x = 0 then ⊤ else ((-WithZero.log x : ℤ) : WithTop ℤ)

@[simp] lemma discreteNegativeLog_zero : discreteNegativeLog 0 = ⊤ := by
  simp [discreteNegativeLog]

@[simp] lemma discreteNegativeLog_one : discreteNegativeLog 1 = 0 := by
  simp [discreteNegativeLog]

@[simp] lemma discreteNegativeLog_exp (n : ℤ) :
    discreteNegativeLog (WithZero.exp n) = ((-n : ℤ) : WithTop ℤ) := by
  simp [discreteNegativeLog]

lemma discreteNegativeLog_le_iff (x y : WithZero (Multiplicative ℤ)) :
    discreteNegativeLog x ≤ discreteNegativeLog y ↔ y ≤ x := by
  by_cases hx : x = 0
  · subst x
    by_cases hy : y = 0
    · simp [hy]
    · simp [discreteNegativeLog, hy]
  by_cases hy : y = 0
  · simp [hy]
  simp only [discreteNegativeLog, ite_eq_right hx, ite_eq_right hy,
    WithTop.coe_le_coe, neg_le_neg_iff]
  exact WithZero.log_le_log hy hx

lemma discreteNegativeLog_lt_iff (x y : WithZero (Multiplicative ℤ)) :
    discreteNegativeLog x < discreteNegativeLog y ↔ y < x := by
  rw [lt_iff_le_not_ge, discreteNegativeLog_le_iff, discreteNegativeLog_le_iff,
    ← lt_iff_le_not_ge]

lemma discreteNegativeLog_mul (x y : WithZero (Multiplicative ℤ)) :
    discreteNegativeLog (x * y) = discreteNegativeLog x + discreteNegativeLog y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  simp only [discreteNegativeLog, ite_eq_right hx, ite_eq_right hy,
    ite_eq_right (mul_ne_zero hx hy),
    WithZero.log_mul hx hy, neg_add, WithTop.coe_add]

/-- Convert a discrete multiplicative valuation to an additive order. -/
def discreteAdditiveOrder {R : Type*} [Ring R]
    (v : Valuation R (WithZero (Multiplicative ℤ))) : AddValuation R (WithTop ℤ) :=
  AddValuation.of (fun x => discreteNegativeLog (v x))
    (by simp) (by simp)
    (fun x y => by
      rcases le_total (v x) (v y) with h | h
      · rw [min_eq_right ((discreteNegativeLog_le_iff _ _).mpr h)]
        exact (discreteNegativeLog_le_iff _ _).mpr
          (by simpa only [max_eq_right h] using v.map_add x y)
      · rw [min_eq_left ((discreteNegativeLog_le_iff _ _).mpr h)]
        exact (discreteNegativeLog_le_iff _ _).mpr
          (by simpa only [max_eq_left h] using v.map_add x y))
    (fun x y => by rw [map_mul, discreteNegativeLog_mul])

@[simp] lemma discreteAdditiveOrder_apply {R : Type*} [Ring R]
    (v : Valuation R (WithZero (Multiplicative ℤ))) (x : R) :
    discreteAdditiveOrder v x = discreteNegativeLog (v x) := rfl

/-- The normalized additive order at a height-one prime. -/
def normalizedBranchOrder {R : Type*} [CommRing R] [IsDedekindDomain R]
    (p : IsDedekindDomain.HeightOneSpectrum R) (L : Type*) [Field L]
    [Algebra R L] [IsFractionRing R L] : AddValuation L (WithTop ℤ) :=
  discreteAdditiveOrder (p.valuation L)

theorem normalizedBranchOrder_nonnegative {R : Type*} [CommRing R] [IsDedekindDomain R]
    (p : IsDedekindDomain.HeightOneSpectrum R) (L : Type*) [Field L]
    [Algebra R L] [IsFractionRing R L] (x : R) :
    0 ≤ normalizedBranchOrder p L (algebraMap R L x) := by
  change 0 ≤ discreteNegativeLog (p.valuation L (algebraMap R L x))
  rw [← discreteNegativeLog_one, discreteNegativeLog_le_iff]
  exact p.valuation_le_one (K := L) x

theorem normalizedBranchOrder_positive_iff {R : Type*} [CommRing R] [IsDedekindDomain R]
    (p : IsDedekindDomain.HeightOneSpectrum R) (L : Type*) [Field L]
    [Algebra R L] [IsFractionRing R L] (x : R) :
    0 < normalizedBranchOrder p L (algebraMap R L x) ↔ x ∈ p.asIdeal := by
  change 0 < discreteNegativeLog (p.valuation L (algebraMap R L x)) ↔ _
  rw [← discreteNegativeLog_one, discreteNegativeLog_lt_iff]
  exact p.valuation_lt_one_iff_mem (K := L) x

theorem normalizedBranchOrder_uniformizer {R : Type*} [CommRing R] [IsDedekindDomain R]
    (p : IsDedekindDomain.HeightOneSpectrum R) (L : Type*) [Field L]
    [Algebra R L] [IsFractionRing R L] :
    ∃ π : L, normalizedBranchOrder p L π = 1 := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer L
  refine ⟨π, ?_⟩
  change discreteNegativeLog (p.valuation L π) = 1
  simp only [hπ, discreteNegativeLog_exp, neg_neg, WithTop.coe_one]

theorem normalizedBranchOrder_parameter {R : Type*} [CommRing R] [IsDedekindDomain R]
    (p : IsDedekindDomain.HeightOneSpectrum R) (L : Type*) [Field L]
    [Algebra R L] [IsFractionRing R L] {x : R} (hx : x ≠ 0) (hp : x ∈ p.asIdeal) :
    ∃ e : ℤ, 0 < e ∧ normalizedBranchOrder p L (algebraMap R L x) = (e : WithTop ℤ) := by
  have hpos := (normalizedBranchOrder_positive_iff p L x).mpr hp
  have hne : algebraMap R L x ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R L).ne hx
  obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp ((normalizedBranchOrder p L).ne_top_iff.mpr hne)
  exact ⟨e, by rw [← he] at hpos; exact_mod_cast hpos, he.symm⟩

end
end PierceLengthBound.FixedDividend
