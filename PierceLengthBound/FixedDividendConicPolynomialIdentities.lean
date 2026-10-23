/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendNormalizedParameter
public import PierceLengthBound.FixedDividendConicLeadingNodes

/-! Actual integral component points force symbolic identities along the bounded
quadratic parameter. At most twenty-four points can avoid this conclusion. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- More than twice the equation degree in integral component points suffices
for a symbolic identity under the actual quadratic parametrization. -/
theorem normalizedParameter_vanishes_of_many_points
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) (σ : Fin 3 ≃ Fin 3)
    {E : ℤ} (hE : E ≠ 0) (F : Fin 3 → Polynomial ℤ)
    (hF : ∀ j, (F j).natDegree ≤ 2) (p : (Fin 3 → ℤ) → ℤ)
    (hrepr : ∀ z : Fin 3 → ℤ, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I →
      ∀ j, E * z (σ j) = (F j).eval (p z))
    (hinj : Set.InjOn p {z | (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I})
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ z ∈ S, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I)
    (f : MvPolynomial (Fin 3) ℚ) (hf : f ∈ I)
    (hc : 2 * f.totalDegree < S.card) :
    MvPolynomial.aeval (normalizedParameter σ E F) f = 0 := by
  let t : S → ℚ := fun z => (p z : ℚ)
  have ht : Function.Injective t := by
    intro z w hzw
    apply Subtype.ext
    apply hinj (hS z z.property) (hS w w.property)
    dsimp only [t] at hzw
    exact_mod_cast hzw
  apply polynomial_substitution_zero_of_many_points _
    (normalizedParameter_degree σ E F hF) f t ht
  · intro z
    have he := normalizedParameter_eval σ hE F z (p z) (hrepr z (hS z z.property))
    dsimp only [t]
    simp_rw [he]
    exact hS z z.property f hf
  · simpa only [Fintype.card_coe] using hc

/-- With at least twenty-five integral points, both actual defining equations
hold symbolically for the normalized parameter produced by the bounded theorem. -/
theorem normalizedParameter_curve_identities
    (ρ u v ρ' u' v' A a : ℚ)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    (σ : Fin 3 ≃ Fin 3) {E : ℤ} (hE : E ≠ 0) (F : Fin 3 → Polynomial ℤ)
    (hF : ∀ j, (F j).natDegree ≤ 2) (p : (Fin 3 → ℤ) → ℤ)
    (hrepr : ∀ z : Fin 3 → ℤ, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I →
      ∀ j, E * z (σ j) = (F j).eval (p z))
    (hinj : Set.InjOn p {z | (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I})
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ z ∈ S, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I)
    (hc : 24 < S.card) :
    MvPolynomial.aeval (normalizedParameter σ E F) (curveQuadratic ρ u v ρ' u' v') = 0 ∧
      MvPolynomial.aeval (normalizedParameter σ E F) (curveEquation ρ u v ρ' u' v' A a) = 0 := by
  constructor
  · apply normalizedParameter_vanishes_of_many_points I σ hE F hF p hrepr hinj S hS _ hf
    have hh := curveQuadratic_degree_le_two ρ u v ρ' u' v'
    omega
  · apply normalizedParameter_vanishes_of_many_points I σ hE F hF p hrepr hinj S hS _ hg
    have hh := curveEquation_degree_le ρ u v ρ' u' v' A a
    omega

end
end PierceLengthBound.FixedDividend
