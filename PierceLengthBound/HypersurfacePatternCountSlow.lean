/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCount
public import PierceLengthBound.FixedDividendCountAssembly

/-! On orbit windows, `hypersurface_pattern_count_tau` gives a proper polynomial
condition the exponent `14/3` with a slowly growing coefficient. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- On the selected starts of an orbit window, the minor patterns satisfying a proper
polynomial condition number at most `R(a) H^(14/3)`, where `H` is the selected minor
height and `R` grows slowly in the dividend `a`. -/
theorem selected_hypersurface_pattern_count_slow {F : MvPolynomial (Fin 10) ℚ}
    (hF : ProperOnMinorCone F) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧
      ∀ {a b s T A : ℕ}, b < a →
        (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
        s + T ≤ P a b → 36 ≤ T →
        ((((selectedStarts a b s T A).image (fun i => plk (Mi a b i))).filter
          (fun p => eval (fun j => (p j : ℚ)) F = 0)).card : ℝ) ≤
          R a * (selectedMinorHeight a A T : ℝ) ^ (14 / 3 : ℝ) := by
  classical
  obtain ⟨K, hK⟩ := hypersurface_pattern_count_tau hF
  refine ⟨fun a => K * (1 + tauMax (10 ^ 16 * a ^ 7) ^ 2),
    (slowGrowth_const K).mul
      (slowGrowth_add (slowGrowth_const 1) ((tauMax_slow (10 ^ 16) 7).pow 2)), ?_⟩
  intro a b s T A hba hmem hsT hT
  have hX := selectedMinorHeight_pos hba hmem hsT hT
  have hbound := hK (selectedMinorHeight a A T) hX
    (((selectedStarts a b s T A).image (fun i => plk (Mi a b i))).filter
      (fun p => eval (fun j => (p j : ℚ)) F = 0)) (by
        intro p hp
        obtain ⟨hp, hz⟩ := mem_filter.mp hp
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
        exact ⟨selectedStart_minor_height hba hmem hsT hi, plucker _, hz⟩)
  refine hbound.trans ?_
  have hτ := hypersurface_tauMax_mono (selectedMinorHeight_le hba hmem hT)
  push_cast
  gcongr
  exact hτ

end
end PierceLengthBound.FixedDividend
