/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.NormCount

/-!
# The definite norm count

For `D ≥ 1` and `N ≠ 0`, the equation `U² + D V² = N` has at most `4 τ(|N|)³` integer
solutions (`norm_count_def`). Write `D = d f²` with `d` squarefree, reduce a solution to a
primitive `u² + d w² = n` with `N = g² n`, and attach the class `t ≡ u w⁻¹ (mod n)`, a square
root of `-d` (the reduction `card_le_of_class_card_le` of `NormCount`, for `-d`). Two solutions
in one class differ by a unit `r + s√-d` with `r² + d s² = 1`, of which there are at most four
(`def_class_units`).
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- The solutions of `U² + D V² = N` in the box `[-B, B]²`. -/
def defSols (D : ℕ) (N : ℤ) (B : ℕ) : Finset (ℤ × ℤ) :=
  (Icc (-(B : ℤ)) B ×ˢ Icc (-(B : ℤ)) B).filter fun p => p.1 ^ 2 + D * p.2 ^ 2 = N

/-- Within one class, all solutions are images of one under the four units. -/
lemma def_class_units {d : ℕ} (hd : 1 ≤ d) {n t : ℤ} (hn : n ≠ 0) (ht : n ∣ t ^ 2 - (-(d : ℤ)))
    {q q' : ℤ × ℤ} (hq : q.1 ^ 2 + d * q.2 ^ 2 = n) (hq' : q'.1 ^ 2 + d * q'.2 ^ 2 = n)
    (hc : n ∣ q.1 - t * q.2) (hc' : n ∣ q'.1 - t * q'.2) :
    ∃ r s : ℤ, (r, s) ∈ ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)) ∧
      q = (q'.1 * r - d * q'.2 * s, q'.1 * s + q'.2 * r) := by
  obtain ⟨u, w⟩ := q
  obtain ⟨u', w'⟩ := q'
  simp only at hq hq' hc hc' ⊢
  have h1 : n ∣ u * u' + d * w * w' := by
    obtain ⟨x, hx⟩ := hc; obtain ⟨y, hy⟩ := hc'; obtain ⟨z, hz⟩ := ht
    exact
        ⟨x * u' + t * w * y + w * w' * z, by linear_combination u' * hx + t * w * hy + w * w' * hz⟩
  have h2 : n ∣ w * u' - u * w' := by
    obtain ⟨x, hx⟩ := hc; obtain ⟨y, hy⟩ := hc'
    exact ⟨w * y - w' * x, by linear_combination w * hy - w' * hx⟩
  obtain ⟨r, hr⟩ := h1
  obtain ⟨s, hs⟩ := h2
  have hnorm : r ^ 2 + d * s ^ 2 = 1 := by
    have : n * n * (r ^ 2 + d * s ^ 2) = n * n * 1 := by
      linear_combination (-(n * r) - (u * u' + d * w * w')) * hr -
        d * (n * s + (w * u' - u * w')) * hs + (u' ^ 2 + d * w' ^ 2) * hq + n * hq'
    exact mul_left_cancel₀ (mul_ne_zero hn hn) this
  have hu : u = u' * r - d * w' * s := by
    apply mul_left_cancel₀ hn
    linear_combination u' * hr - d * w' * hs - u * hq'
  have hw : w = u' * s + w' * r := by
    apply mul_left_cancel₀ hn
    linear_combination u' * hs + w' * hr - w * hq'
  refine ⟨r, s, ?_, by rw [hu, hw]⟩
  have hs2 : d * s ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
  have hr1 : -1 ≤ r ∧ r ≤ 1 := by constructor <;> nlinarith
  have hs1 : -1 ≤ s ∧ s ≤ 1 := by
    have : s ^ 2 ≤ 1 := by nlinarith
    constructor <;> nlinarith
  simp only [mem_insert, mem_singleton, Prod.mk.injEq]
  have : r = -1 ∨ r = 0 ∨ r = 1 := by omega
  have : s = -1 ∨ s = 0 ∨ s = 1 := by omega
  rcases this with h | h | h <;> rcases ‹r = -1 ∨ r = 0 ∨ r = 1› with h' | h' | h' <;>
    subst h <;> subst h'
  all_goals (try norm_num at hnorm ⊢)
  all_goals omega

/-- **The definite norm count.** For `D ≥ 1` and `N ≠ 0`, the equation `U² + D V² = N` has at
most `4 τ(|N|)³` solutions in any box `[-B, B]²`. -/
theorem norm_count_def {D : ℕ} {N : ℤ} (B : ℕ) (hD : 1 ≤ D) (hN : N ≠ 0) :
    (defSols D N B).card ≤ 4 * N.natAbs.divisors.card ^ 3 := by
  obtain ⟨d, f, hd0, hf0, hDf, hsf⟩ := Nat.sq_mul_squarefree_of_pos (by omega : 0 < D)
  subst hDf
  -- the definite equation is the norm equation for `-d`, with a single label
  refine (card_le_of_class_card_le (d := -(d : ℤ))
    (fun y hy => Int.squarefree_natCast.mpr hsf y (dvd_neg.mp hy)) hf0 hN
    (fun p hp => by have := (mem_filter.mp hp).2; push_cast at this; linear_combination this)
    (fun _ => ()) 4 fun n t hn ht _ Q hQ => ?_).trans (by simp)
  -- every reduced solution in the class is a unit multiple of a fixed one
  rcases Q.eq_empty_or_nonempty with rfl | ⟨q0, hq0⟩
  · simp
  obtain ⟨-, hc0, _, -, _, R0⟩ := hQ q0 hq0
  have hsub : Q ⊆ ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)).image fun rs =>
      (q0.1 * rs.1 - d * q0.2 * rs.2, q0.1 * rs.2 + q0.2 * rs.1) := by
    intro q hq
    obtain ⟨-, hc, _, -, _, R⟩ := hQ q hq
    obtain ⟨r, s, hrs, he⟩ := def_class_units hd0 hn ht (by rw [R.hn]; ring)
      (by rw [R0.hn]; ring) hc hc0
    exact mem_image.mpr ⟨(r, s), hrs, he.symm⟩
  exact (card_le_card hsub).trans (card_image_le.trans (by decide))

end PierceLengthBound
