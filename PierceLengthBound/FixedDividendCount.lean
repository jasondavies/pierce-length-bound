/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.OrbitPattern

/-!
# Multiplicity of patterns and gap vectors

Fixed minors and five gaps determine a nonzero quartic in the quotient. Thus at
most four orbit starts have these data.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- At most four starts have a prescribed pair of minor pattern and gap vector. -/
theorem pattern_gap_multiplicity {G : Finset ℕ} {θ : ℕ → Fin 7 → ℤ}
    {κ : ℕ → Fin 5 → ℤ} {pm : ℕ → Fin 10 → ℤ} {Q : ℕ → ℤ} {a : ℤ}
    (hθ : ∀ i ∈ G, θ i = projθ (pm i)) (hQ : Set.InjOn Q G)
    (h0 : ∀ i ∈ G, 1 ≤ θ i 0)
    (hm : ∀ i ∈ G, quart (-θ i 1) (θ i 3) (θ i 4) (θ i 0)
      (κ i 0) (κ i 1) (κ i 2) (Q i) =
      a * muH4 (κ i 0) (κ i 1) (κ i 2) (κ i 3) (κ i 4)) :
    G.card ≤ 4 * (G.image fun i => (pm i, κ i)).card := by
  classical
  set F : ℕ → (Fin 10 → ℤ) × (Fin 5 → ℤ) := fun i => (pm i, κ i)
  refine card_le_mul_card_image G 4 fun v _ => ?_
  set S := G.filter fun i => F i = v
  rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
  · rw [hS]; simp
  have hi₀' := mem_filter.mp hi₀
  rw [← card_image_of_injOn (hQ.mono (fun x hx => (mem_filter.mp hx).1))]
  have hlead : θ i₀ 0 ≠ 0 := by have := h0 i₀ hi₀'.1; omega
  refine card_le_four_of_quartic
    (c3 := quartC (-θ i₀ 1) (θ i₀ 3) (θ i₀ 4) (θ i₀ 0) (κ i₀ 0) (κ i₀ 1) (κ i₀ 2) 3)
    (c2 := quartC (-θ i₀ 1) (θ i₀ 3) (θ i₀ 4) (θ i₀ 0) (κ i₀ 0) (κ i₀ 1) (κ i₀ 2) 2)
    (c1 := quartC (-θ i₀ 1) (θ i₀ 3) (θ i₀ 4) (θ i₀ 0) (κ i₀ 0) (κ i₀ 1) (κ i₀ 2) 1)
    (c0 := quartC (-θ i₀ 1) (θ i₀ 3) (θ i₀ 4) (θ i₀ 0) (κ i₀ 0) (κ i₀ 1) (κ i₀ 2) 0 -
      a * muH4 (κ i₀ 0) (κ i₀ 1) (κ i₀ 2) (κ i₀ 3) (κ i₀ 4)) hlead fun z hz => ?_
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
  obtain ⟨hiG, hFi⟩ := mem_filter.mp hi
  have hF : F i = F i₀ := hFi.trans hi₀'.2.symm
  simp only [F, Prod.mk.injEq] at hF
  have hθi : θ i = θ i₀ := by rw [hθ i hiG, hθ i₀ hi₀'.1, hF.1]
  have := hm i hiG
  rw [quart_eq, hθi, hF.2] at this
  linarith

/-- Distinct data split into the distinct gap vectors above each pattern. -/
lemma pair_image_card_le_sum {ι α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : Finset ι) (p : ι → α) (k : ι → β) :
    (G.image fun i => (p i, k i)).card ≤
      ∑ v ∈ G.image p, ((G.filter fun i => p i = v).image k).card := by
  classical
  let F := G.image fun i => (p i, k i)
  have he : F.card = ∑ v ∈ G.image p, (F.filter fun w => w.1 = v).card :=
    card_eq_sum_card_fiberwise fun w hw => by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hw
      exact mem_image.mpr ⟨i, hi, rfl⟩
  rw [show (G.image fun i => (p i, k i)) = F from rfl, he]
  apply sum_le_sum
  intro v _
  apply card_le_card_of_injOn Prod.snd
  · intro w hw
    obtain ⟨hwF, hwv⟩ := mem_filter.mp hw
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hwF
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, hwv⟩, rfl⟩
  · intro w hw w' hw' hh
    exact Prod.ext ((mem_filter.mp hw).2.trans (mem_filter.mp hw').2.symm) hh

end PierceLengthBound.FixedDividend
