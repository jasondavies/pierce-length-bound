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
# Nonexceptional directions

The leading moment equations force all five nodes to be distinct for a
nonexceptional pattern.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

/-- Nonexceptionality in terms of the four exact coefficient relations. -/
def NonexceptionalPattern (ρ u v : ℝ) : Prop :=
  ∀ d : Fin 4, ¬exceptionalRelation ρ u v d

/-- Over any field, if all weights and all pair sums are nonzero, a nonconstant
solution of the first four moment equations has distinct entries. -/
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

end PierceLengthBound.FixedDividend
