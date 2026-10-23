/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Data.Multiset.MapFold
import Mathlib.Tactic

/-! Monic factors in a specialized splitting algebra lift to monic factors
before specialization. Multiplicities are tracked by multisets, so this
does not require excluding the discriminant-zero parameters. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

theorem branch_submultiset_lifts {α β : Type*} (f : α → β)
    {s : Multiset α} {t : Multiset β} (ht : t ≤ s.map f) :
    ∃ u : Multiset α, u ≤ s ∧ u.map f = t := by
  classical
  induction t using Multiset.induction_on generalizing s with
  | empty => exact ⟨0, by simp, by simp⟩
  | @cons b t ih =>
    have hb : b ∈ s.map f := Multiset.mem_of_le ht (Multiset.mem_cons_self b t)
    obtain ⟨a, ha, hab⟩ := Multiset.mem_map.mp hb
    have hs : a ::ₘ s.erase a = s := Multiset.cons_erase ha
    have htail : t ≤ (s.erase a).map f := by
      rw [← hs, Multiset.map_cons, hab] at ht
      exact (Multiset.cons_le_cons_iff b).mp ht
    obtain ⟨u, hu, hmap⟩ := ih htail
    refine ⟨a ::ₘ u, ?_, ?_⟩
    · rw [← hs]
      exact Multiset.cons_le_cons _ hu
    · simp only [Multiset.map_cons, hab, hmap]

variable {R K : Type*} [CommRing R] [IsDomain R] [CommRing K] [IsDomain K]

/-- Every monic divisor after reduction lifts to a monic divisor of the split
polynomial before reduction. The lifted factor has exactly the same degree. -/
theorem branch_split_monic_factor_lifts (φ : R →+* K) {p : R[X]}
    (hp : p.Monic) (hsplit : p.Splits) {q : K[X]}
    (hq : q.Monic) (hdiv : q ∣ p.map φ) :
    ∃ q₀ : R[X], q₀.Monic ∧ q₀ ∣ p ∧ q₀.map φ = q ∧ q₀.natDegree = q.natDegree := by
  classical
  have hpmap : p.map φ ≠ 0 := (hp.map φ).ne_zero
  have hqsplit := (hsplit.map φ).of_dvd hpmap hdiv
  have hroots : q.roots ≤ p.roots.map φ := by
    rw [← hsplit.roots_map_of_ne_zero hpmap]
    exact Polynomial.roots.le_of_dvd hpmap hdiv
  obtain ⟨u, hu, humap⟩ := branch_submultiset_lifts φ hroots
  let q₀ : R[X] := (u.map (fun a => X - C a)).prod
  have hq₀ : q₀.Monic := Polynomial.monic_multisetProd_X_sub_C u
  have hq₀div : q₀ ∣ p := by
    rw [hsplit.eq_prod_roots_of_monic hp]
    exact Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hu)
  have hq₀map : q₀.map φ = q := by
    rw [hqsplit.eq_prod_roots_of_monic hq, ← humap]
    simp only [q₀, Polynomial.map_multiset_prod, Multiset.map_map,
      Function.comp_def, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  refine ⟨q₀, hq₀, hq₀div, hq₀map, ?_⟩
  rw [← hq₀map, hq₀.natDegree_map]

end
end PierceLengthBound.FixedDividend
