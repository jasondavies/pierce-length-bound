/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendDirections
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Nonexceptional directions and local parity

The leading moment equations force all five nodes to be distinct for a
nonexceptional pattern. A square times a unit equal to a fourth power has even
order in every discrete valuation ring. These are local ingredients of the
180/611 candidate; identifying their sum with the filtered Hilbert degree is a
separate geometric obligation.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

/-- Nonexceptionality in terms of the four exact coefficient relations. -/
def NonexceptionalPattern (ρ u v : ℝ) : Prop :=
  ∀ d : Fin 4, ¬exceptionalRelation ρ u v d

/-- The collision obstruction is algebraic over any field; no closure or ordering
is needed once individual and pair coefficient sums are nonzero. -/
theorem leading_nodes_injective_of_pair_sums_ne_zero {K : Type*} [Field K]
    (c z : Fin 5 → K) (hc : ∀ j, c j ≠ 0)
    (hp : ∀ j l, j < l → c j + c l ≠ 0) (hz : ∃ i j, z i ≠ z j)
    (hmom : ∀ m < 4, ∑ j : Fin 5, c j * z j ^ m = 0) :
    Function.Injective z := by
  classical
  intro j l heq
  by_contra hjl
  have hs := cluster_sums_zero_field c z (direction_card_of_collision z hjl heq) hmom
  obtain ⟨i, k, hik, hsum, _⟩ := exists_pair_cluster c z hc hz hs
  exact hp i k hik hsum

/-- Nonexceptionality is exactly nonvanishing of every distinct coefficient pair. -/
theorem nonexceptional_iff_pair_sums_ne_zero {ρ u v : ℝ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) :
    NonexceptionalPattern ρ u v ↔
      ∀ j l : Fin 5, j < l → coeffs ρ u v j + coeffs ρ u v l ≠ 0 := by
  constructor
  · intro hn j l hjl heq
    rcases pair_indices_exceptional hρ hu hv hjl heq with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hn 0 (exceptionalRelation_of_pair 0 heq)
    · exact hn 1 (exceptionalRelation_of_pair 1 heq)
    · exact hn 2 (exceptionalRelation_of_pair 2 heq)
    · exact hn 3 (exceptionalRelation_of_pair 3 heq)
  · intro hp d hd
    fin_cases d
    · apply hp 0 3 (by decide)
      norm_num [exceptionalRelation, coeffs] at hd ⊢
      linarith
    · apply hp 1 2 (by decide)
      norm_num [exceptionalRelation, coeffs] at hd ⊢
      linarith
    · apply hp 2 3 (by decide)
      norm_num [exceptionalRelation, coeffs] at hd ⊢
      linarith
    · apply hp 1 4 (by decide)
      norm_num [exceptionalRelation, coeffs] at hd ⊢
      linarith

/-- Every node is distinct at a nonzero leading solution of a nonexceptional pattern. -/
theorem nonexceptional_leading_nodes_injective {ρ u v : ℝ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern ρ u v)
    (z : Fin 5 → ℂ) (hz : ∃ i j, z i ≠ z j) (hz0 : z 0 = 0)
    (hmom : ∀ m < 4, ∑ j : Fin 5, (coeffs ρ u v j : ℂ) * z j ^ m = 0) :
    Function.Injective z := by
  intro j l heq
  by_contra hjl
  obtain ⟨d, t, ht, hdir, hrel⟩ := complex_direction_classification hρ hu hv z hz hz0
    (direction_card_of_collision z hjl heq) hmom
  exact hne d hrel

/-- In particular the degree-ten resultant form does not vanish at infinity. -/
theorem nonexceptional_leading_vandermonde_ne_zero {ρ u v : ℝ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern ρ u v)
    (z : Fin 5 → ℂ) (hz : ∃ i j, z i ≠ z j) (hz0 : z 0 = 0)
    (hmom : ∀ m < 4, ∑ j : Fin 5, (coeffs ρ u v j : ℂ) * z j ^ m = 0) :
    nodeVandermonde (fun j : Fin 4 => z j.succ) ≠ 0 := by
  intro hV
  obtain ⟨d, t, ht, hdir, hrel⟩ :=
    complex_direction_of_leading_equations hρ hu hv z hz hz0 hV hmom
  exact hne d hrel

/-- Exact valuation identity for the homogenized square/fourth-power equation. -/
theorem dvr_order_square_unit_eq_fourth {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {A a r h δ : R}
    (hA : IsUnit A) (ha : IsUnit a) (hr : IsUnit r)
    (heq : A * h ^ 2 * r = a * δ ^ 4) :
    2 • IsDiscreteValuationRing.addVal R h =
      4 • IsDiscreteValuationRing.addVal R δ := by
  have h := congrArg (IsDiscreteValuationRing.addVal R) heq
  simpa only [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hA,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr ha,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hr, zero_add, add_zero] using h

/-- Every finite order of the infinity coordinate is even, with its exact half. -/
theorem dvr_order_even_of_square_unit_eq_fourth {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {A a r h δ : R}
    (hA : IsUnit A) (ha : IsUnit a) (hr : IsUnit r) (hh : h ≠ 0)
    (heq : A * h ^ 2 * r = a * δ ^ 4) :
    ∃ n : ℕ, IsDiscreteValuationRing.addVal R h = (2 * n : ℕ) ∧
      IsDiscreteValuationRing.addVal R δ = n := by
  have hhfin : IsDiscreteValuationRing.addVal R h ≠ ⊤ := by
    exact fun htop => hh (IsDiscreteValuationRing.addVal_eq_top_iff.mp htop)
  have hδ : δ ≠ 0 := by
    intro hδ
    have : A * h ^ 2 * r ≠ 0 := mul_ne_zero (mul_ne_zero hA.ne_zero (pow_ne_zero _ hh))
      hr.ne_zero
    apply this
    simpa [hδ] using heq
  have hδfin : IsDiscreteValuationRing.addVal R δ ≠ ⊤ := by
    exact fun htop => hδ (IsDiscreteValuationRing.addVal_eq_top_iff.mp htop)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hhfin
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hδfin
  have hv := dvr_order_square_unit_eq_fourth hA ha hr heq
  rw [← hm, ← hn] at hv
  have hmn : 2 * m = 4 * n := by
    simpa only [nsmul_eq_mul, ← Nat.cast_mul, ENat.natCast_inj] using hv
  refine ⟨n, ?_, hn.symm⟩
  rw [← hm]
  congr 1
  omega

/-- The same identity for intersection lengths needs no normality or smoothness. -/
theorem local_length_square_unit_eq_fourth {R : Type*} [CommRing R] [IsDomain R]
    {A a r h δ : R} (hA : IsUnit A) (ha : IsUnit a) (hr : IsUnit r)
    (hh : h ≠ 0) (heq : A * h ^ 2 * r = a * δ ^ 4) :
    2 • Ring.ord R h = 4 • Ring.ord R δ := by
  have hδ : δ ≠ 0 := by
    intro hδ
    have : A * h ^ 2 * r ≠ 0 := mul_ne_zero (mul_ne_zero hA.ne_zero (pow_ne_zero _ hh))
      hr.ne_zero
    exact this (by simpa [hδ] using heq)
  have hv := congrArg (Ring.ord R) heq
  simpa only [Ring.ord_mul_of_isUnit_right hr, Ring.ord_mul_of_isUnit_left hA,
    Ring.ord_mul_of_isUnit_left ha,
    Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.mpr hh),
    Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.mpr hδ)] using hv

/-- In a one-dimensional Noetherian domain the local infinity intersection length
is a finite even integer. This also covers singular local rings. -/
theorem local_length_even_of_square_unit_eq_fourth {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {A a r h δ : R} (hA : IsUnit A) (ha : IsUnit a) (hr : IsUnit r)
    (hh : h ≠ 0) (heq : A * h ^ 2 * r = a * δ ^ 4) :
    ∃ n : ℕ, Module.length R (R ⧸ Ideal.span {h}) = (2 * n : ℕ) := by
  have hv := local_length_square_unit_eq_fourth hA ha hr hh heq
  have hhfin := Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hh)
  have hδ : δ ≠ 0 := by
    intro hδ
    have : A * h ^ 2 * r ≠ 0 := mul_ne_zero (mul_ne_zero hA.ne_zero (pow_ne_zero _ hh))
      hr.ne_zero
    exact this (by simpa [hδ] using heq)
  have hδfin := Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hδ)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hhfin
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hδfin
  rw [← hm, ← hn] at hv
  have hmn : 2 * m = 4 * n := by
    simpa only [nsmul_eq_mul, ← Nat.cast_mul, ENat.natCast_inj] using hv
  refine ⟨n, ?_⟩
  change Ring.ord R h = _
  rw [← hm]
  congr 1
  omega

end PierceLengthBound.FixedDividend
