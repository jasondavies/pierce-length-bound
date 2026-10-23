/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCountSlow
public import PierceLengthBound.PolarProjectionCountAssembly

/-! The proper algebraic degeneracy locus is included in the actual bad-pattern
count, together with any previously counted specialization exceptions. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- Combining two good-pattern conditions adds their bad-pattern coefficients. -/
theorem PolarBadPatternCount.inter
    {good₁ good₂ : ℕ → (Fin 10 → ℤ) → Prop} {R₁ R₂ : ℕ → ℕ}
    (h₁ : PolarBadPatternCount good₁ R₁) (h₂ : PolarBadPatternCount good₂ R₂) :
    PolarBadPatternCount (fun a p => good₁ a p ∧ good₂ a p) (fun a => R₁ a + R₂ a) := by
  classical
  intro a b s T A hba hmem hsT hT
  let S := (selectedStarts a b s T A).image (fun i => plk (Mi a b i))
  have hsub : S.filter (fun p => ¬ (good₁ a p ∧ good₂ a p)) ⊆
      S.filter (fun p => ¬ good₁ a p) ∪ S.filter (fun p => ¬ good₂ a p) := by
    intro p hp
    obtain ⟨hp, hn⟩ := mem_filter.mp hp
    by_cases hgood : good₁ a p
    · exact mem_union_right _ (mem_filter.mpr ⟨hp, fun h => hn ⟨hgood, h⟩⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hp, hgood⟩)
  have hcard : ((S.filter (fun p => ¬ (good₁ a p ∧ good₂ a p))).card : ℝ) ≤
      (S.filter (fun p => ¬ good₁ a p)).card + (S.filter (fun p => ¬ good₂ a p)).card := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have hcount₁ := h₁ hba hmem hsT hT
  have hcount₂ := h₂ hba hmem hsT hT
  have hsum := hcard.trans (add_le_add hcount₁ hcount₂)
  simpa only [S, Nat.cast_add, add_mul] using hsum

/-- The complement of any proper fixed hypersurface has the required actual
bad-pattern bound with a slowly growing coefficient. -/
theorem polarBadPatternCount_hypersurface {F : MvPolynomial (Fin 10) ℚ}
    (hF : ProperOnMinorCone F) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧
      PolarBadPatternCount (fun _ p => eval (fun j => (p j : ℚ)) F ≠ 0) R := by
  obtain ⟨R, hR, hcount⟩ := selected_hypersurface_pattern_count_slow hF
  refine ⟨R, hR, ?_⟩
  intro a b s T A hba hmem hsT hT
  simpa only [not_not] using hcount hba hmem hsT hT

/-- Adding the new proper algebraic degeneracy locus to a counted branch-sieve
exception class preserves the exact 14/3 pattern exponent. -/
theorem polarBadPatternCount_add_hypersurface
    {good : ℕ → (Fin 10 → ℤ) → Prop} {R : ℕ → ℕ}
    (hR : SlowGrowth R) (hbad : PolarBadPatternCount good R)
    {F : MvPolynomial (Fin 10) ℚ} (hF : ProperOnMinorCone F) :
    ∃ R' : ℕ → ℕ, SlowGrowth R' ∧
      PolarBadPatternCount
        (fun a p => good a p ∧ eval (fun j => (p j : ℚ)) F ≠ 0) R' := by
  obtain ⟨R₂, hR₂, hbad₂⟩ := polarBadPatternCount_hypersurface hF
  exact ⟨fun a => R a + R₂ a, slowGrowth_add hR hR₂, hbad.inter hbad₂⟩

end
end PierceLengthBound.FixedDividend
