/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.TwoState

/-!
# The counting lemma

Let `G` be a finite set of states, each carrying a *pattern* `θ ∈ ℤ⁷` with `|θₜ| ≤ M`, gaps
`κ ∈ [1, H]⁵` and a quotient `Q`, injective on `G`, satisfying the two-state relations:
the linear relations at `i` and `i+1`, the quadratic relation at `i`, and the multiplicity
identity. Then `#G ≤ 8 (2M+1)⁷ H²`.

* A fixed `(θ, κ)` fixes a quartic with leading coefficient `θ₀ ≥ 1` vanishing at every `Q`:
  at most `4` states.
* A fixed `(θ, κ₁, κ₂)` leaves at most two values of `κ₃` (the reduced quadratic has leading
  coefficient `θ₁ θ₀ (θ₁ + θ₀) > 0`), and `κ₀, κ₄` are then fixed by the linear relations.
* There are at most `(2M+1)⁷ H²` values of `(θ, κ₁, κ₂)`.
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- **The counting lemma.** States with injective quotients `Q`, patterns `|θₜ| ≤ M` with
`θ₀, θ₁ ≥ 1`, gaps in `[1, H]`, the two `k`-relations, the `r`-relation and the multiplicity
identity number at most `8 (2M+1)⁷ H²`. -/
theorem pattern_count {G : Finset ℕ} {θ : ℕ → Fin 7 → ℤ} {κ : ℕ → Fin 5 → ℤ} {Q : ℕ → ℤ}
    {a : ℤ} {M H : ℕ}
    (hQ : Set.InjOn Q G)
    (hθ : ∀ i ∈ G, ∀ t, |θ i t| ≤ M)
    (hκ : ∀ i ∈ G, ∀ t, 1 ≤ κ i t ∧ κ i t ≤ H)
    (h0 : ∀ i ∈ G, 1 ≤ θ i 0) (h1 : ∀ i ∈ G, 1 ≤ θ i 1)
    (e0 : ∀ i ∈ G, -θ i 1 * κ i 0 + θ i 3 * κ i 1 + θ i 4 * κ i 2 + θ i 0 * κ i 3 = 0)
    (e4 : ∀ i ∈ G, -θ i 2 * κ i 1 + θ i 5 * κ i 2 + θ i 6 * κ i 3 + θ i 1 * κ i 4 = 0)
    (e3 : ∀ i ∈ G, -θ i 1 * (κ i 0 ^ 2 + κ i 1) + θ i 3 * (κ i 1 * (2 * κ i 0 + κ i 1) + κ i 2) +
      θ i 4 * (κ i 2 * (2 * κ i 0 + 2 * κ i 1 + κ i 2) + κ i 3) +
      θ i 0 * (κ i 3 * (2 * κ i 0 + 2 * κ i 1 + 2 * κ i 2 + κ i 3) + κ i 4) = 0)
    (hm : ∀ i ∈ G, quart (-θ i 1) (θ i 3) (θ i 4) (θ i 0) (κ i 0) (κ i 1) (κ i 2) (Q i) =
      a * muH4 (κ i 0) (κ i 1) (κ i 2) (κ i 3) (κ i 4)) :
    G.card ≤ 8 * (2 * M + 1) ^ 7 * H ^ 2 := by
  classical
  set F : ℕ → (Fin 7 → ℤ) × (Fin 5 → ℤ) := fun i => (θ i, κ i)
  set π : (Fin 7 → ℤ) × (Fin 5 → ℤ) → (Fin 7 → ℤ) × ℤ × ℤ := fun v => (v.1, v.2 1, v.2 2)
  -- step 1: at most four states per `(θ, κ)`
  have step1 : G.card ≤ 4 * (G.image F).card := by
    refine card_le_mul_card_image G 4 fun v hv => ?_
    set S := G.filter fun i => F i = v
    rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
    · rw [hS]; simp
    have hi₀' := (mem_filter.mp hi₀)
    rw [← card_image_of_injOn (hQ.mono (fun x hx => (mem_filter.mp hx).1))]
    have hlead : v.1 0 ≠ 0 := by
      rw [← hi₀'.2]; have := h0 i₀ hi₀'.1; simp only [F]; omega
    refine card_le_four_of_quartic (c3 := quartC (-v.1 1) (v.1 3) (v.1 4) (v.1 0) (v.2 0) (v.2 1)
      (v.2 2) 3) (c2 := quartC (-v.1 1) (v.1 3) (v.1 4) (v.1 0) (v.2 0) (v.2 1) (v.2 2) 2)
      (c1 := quartC (-v.1 1) (v.1 3) (v.1 4) (v.1 0) (v.2 0) (v.2 1) (v.2 2) 1)
      (c0 := quartC (-v.1 1) (v.1 3) (v.1 4) (v.1 0) (v.2 0) (v.2 1) (v.2 2) 0 -
        a * muH4 (v.2 0) (v.2 1) (v.2 2) (v.2 3) (v.2 4)) hlead fun z hz => ?_
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    obtain ⟨hiG, hFi⟩ := mem_filter.mp hi
    have := hm i hiG
    rw [quart_eq] at this
    rw [← hFi]
    simp only [F]
    linarith
  -- step 2: at most two `κ` per `(θ, κ₁, κ₂)`
  have step2 : (G.image F).card ≤ 2 * ((G.image F).image π).card := by
    refine card_le_mul_card_image _ 2 fun w hw => ?_
    set S := (G.image F).filter fun v => π v = w
    rcases S.eq_empty_or_nonempty with hS | ⟨v₀, hv₀⟩
    · rw [hS]; simp
    -- every element of `S` comes from a state
    have hS : ∀ v ∈ S, ∃ i ∈ G, F i = v ∧ π v = w := by
      intro v hv
      obtain ⟨hvF, hvw⟩ := mem_filter.mp hv
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hvF
      exact ⟨i, hi, rfl, hvw⟩
    have hinj : Set.InjOn (fun v : (Fin 7 → ℤ) × (Fin 5 → ℤ) => v.2 3) S := by
      intro v hv v' hv' h3
      obtain ⟨i, hi, rfl, hw⟩ := hS v hv
      obtain ⟨i', hi', rfl, hw'⟩ := hS v' hv'
      have hww : π (F i) = π (F i') := hw.trans hw'.symm
      simp only [F, π, Prod.mk.injEq] at hww h3 ⊢
      obtain ⟨hθ', k1, k2⟩ := hww
      refine ⟨hθ', ?_⟩
      have hN : θ i 1 ≠ 0 := by have := h1 i hi; omega
      have a0 := e0 i hi
      have a0' := e0 i' hi'
      have a4 := e4 i hi
      have a4' := e4 i' hi'
      rw [← hθ', ← k1, ← k2, ← h3] at a0' a4'
      have k0 : κ i 0 = κ i' 0 := by
        have : θ i 1 * κ i 0 = θ i 1 * κ i' 0 := by linarith
        exact mul_left_cancel₀ hN this
      have k4 : κ i 4 = κ i' 4 := by
        have : θ i 1 * κ i 4 = θ i 1 * κ i' 4 := by linarith
        exact mul_left_cancel₀ hN this
      funext t
      fin_cases t
      · exact k0
      · exact k1
      · exact k2
      · exact h3
      · exact k4
    obtain ⟨i₀, hi₀, hF₀, hw₀⟩ := hS v₀ hv₀
    rw [← card_image_of_injOn hinj]
    have hα : w.1 1 * w.1 0 * (w.1 1 + w.1 0) ≠ 0 := by
      rw [← hw₀, ← hF₀]
      simp only [F, π]
      have := h0 i₀ hi₀; have := h1 i₀ hi₀
      positivity
    refine card_le_two_of_quad (β := qB (w.1 0) (w.1 1) (w.1 2) (w.1 3) (w.1 4) (w.1 5) (w.1 6)
      w.2.1 w.2.2) (γ := qC (w.1 0) (w.1 1) (w.1 2) (w.1 3) (w.1 4) (w.1 5) (w.1 6) w.2.1 w.2.2)
      hα fun z hz => ?_
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hz
    obtain ⟨i, hi, rfl, hw⟩ := hS v hv
    rw [← hw]
    simp only [F, π]
    exact quad_root (e0 i hi) (e4 i hi) (e3 i hi)
  -- step 3: the box
  have step3 : ((G.image F).image π).card ≤ (2 * M + 1) ^ 7 * H ^ 2 := by
    set B : Finset ((Fin 7 → ℤ) × ℤ × ℤ) :=
      Fintype.piFinset (fun _ => Icc (-(M : ℤ)) M) ×ˢ (Icc (1 : ℤ) H ×ˢ Icc (1 : ℤ) H)
    have hsub : (G.image F).image π ⊆ B := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
      simp only [B, F, π, mem_product, Fintype.mem_piFinset, mem_Icc]
      refine ⟨fun t => abs_le.mp (hθ i hi t), ⟨(hκ i hi 1).1, (hκ i hi 1).2⟩,
        ⟨(hκ i hi 2).1, (hκ i hi 2).2⟩⟩
    calc ((G.image F).image π).card ≤ B.card := card_le_card hsub
      _ = (2 * M + 1) ^ 7 * H ^ 2 := by
        simp only [B, card_product, Fintype.card_piFinset, Int.card_Icc, prod_const, card_univ,
          Fintype.card_fin]
        have e1 : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
        have e2 : ((H : ℤ) + 1 - 1).toNat = H := by omega
        rw [e1, e2]; ring
  calc G.card ≤ 4 * (G.image F).card := step1
    _ ≤ 4 * (2 * ((G.image F).image π).card) := Nat.mul_le_mul_left _ step2
    _ ≤ 4 * (2 * ((2 * M + 1) ^ 7 * H ^ 2)) := by gcongr
    _ = 8 * (2 * M + 1) ^ 7 * H ^ 2 := by ring

end PierceLengthBound
