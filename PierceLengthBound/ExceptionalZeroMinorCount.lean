/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ExceptionalRankOneCount

/-! Counting minor vectors with a vanishing first maximal minor (Lemma 8.5). By Grassmann
duality the nine remaining minors form three vectors `x, y, z ∈ ℤ³` with `x × y = 0` and
`x ⬝ᵥ z = y ⬝ᵥ z = 0`, which are counted in `rank_one_orthogonal_count`. -/

@[expose] public section
namespace PierceLengthBound
open Finset
open scoped Matrix
open Matrix (vec3_dotProduct)

/-- Hodge-dual coordinates when the first maximal minor vanishes. -/
def zeroMinorCoordinates (p : Fin 10 → ℤ) :
    (Fin 3 → ℤ) × (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
  (![p 7, -p 4, p 2], ![-p 6, p 3, -p 1], ![p 5, p 8, p 9])

/-- The zero minor gives the rank-one and orthogonality equations exactly. -/
theorem zero_minor_equations {p : Fin 10 → ℤ} (h : PluckerRel p) (h0 : p 0 = 0) :
    (∀ j, ((zeroMinorCoordinates p).1 ⨯₃ (zeroMinorCoordinates p).2.1) j = 0) ∧
      (zeroMinorCoordinates p).1 ⬝ᵥ (zeroMinorCoordinates p).2.2 = 0 ∧
      (zeroMinorCoordinates p).2.1 ⬝ᵥ (zeroMinorCoordinates p).2.2 = 0 := by
  constructor
  · intro j
    have he := h 0 j
    fin_cases j <;> norm_num [zeroMinorCoordinates, cross_apply_cyc, uVec, vVec, puX, puS,
      pvX, pvS, pwX, pwS, h0] at he ⊢ <;> linear_combination -he
  · have ha := h 2 2
    have hb := h 1 2
    norm_num [zeroMinorCoordinates, vec3_dotProduct, cross_apply_cyc, uVec, vVec, puX, puS,
      pvX, pvS, pwX, pwS] at ha hb ⊢
    constructor
    · linear_combination ha
    · linear_combination -hb

/-- The nine Hodge-dual coordinates determine every vector whose first minor is zero. -/
theorem zeroMinorCoordinates_inj {p q : Fin 10 → ℤ} (hp : p 0 = 0) (hq : q 0 = 0)
    (he : zeroMinorCoordinates p = zeroMinorCoordinates q) : p = q := by
  have ha := congrArg Prod.fst he
  have hb := congrArg (fun x => x.2.1) he
  have ht := congrArg (fun x => x.2.2) he
  have ha0 := congrFun ha 0
  have ha1 := congrFun ha 1
  have ha2 := congrFun ha 2
  have hb0 := congrFun hb 0
  have hb1 := congrFun hb 1
  have hb2 := congrFun hb 2
  have ht0 := congrFun ht 0
  have ht1 := congrFun ht 1
  have ht2 := congrFun ht 2
  dsimp [zeroMinorCoordinates] at ha0 ha1 ha2 hb0 hb1 hb2 ht0 ht1 ht2
  simp only [neg_inj] at ha1 hb0 hb2
  funext j
  fin_cases j <;> first | exact hp.trans hq.symm | assumption

/-- Integral minor vectors of height `≤ X` satisfying the Plücker relations with first minor
zero number at most `(2X + 1)³ + (log₂ X + 1) · 273375 X⁴`. -/
theorem zero_minor_vector_count {S : Finset (Fin 10 → ℤ)} {X : ℕ} (hX : 1 ≤ X)
    (hS : ∀ p ∈ S, (∀ j, |p j| ≤ X) ∧ PluckerRel p ∧ p 0 = 0) :
    S.card ≤ (2 * X + 1) ^ 3 + (Nat.log 2 X + 1) * (273375 * X ^ 4) := by
  classical
  have hi : Set.InjOn zeroMinorCoordinates S := by
    intro p hp q hq he
    exact zeroMinorCoordinates_inj (hS p hp).2.2 (hS q hq).2.2 he
  have he := rank_one_orthogonal_count (S := S.image zeroMinorCoordinates) hX (by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
    obtain ⟨hb, hpl, hz⟩ := hS p hp
    have eqs := zero_minor_equations hpl hz
    refine ⟨?_, ?_, ?_, eqs⟩
    all_goals intro j; fin_cases j <;> dsimp [zeroMinorCoordinates] <;>
      (try simp only [abs_neg]) <;> apply hb)
  rwa [card_image_of_injOn hi] at he

end PierceLengthBound
