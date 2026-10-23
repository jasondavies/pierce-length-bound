/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ChartDiscreteOrders
public import PierceLengthBound.FixedDividendChartResultant

/-! # Resultant and rank-five orders at infinity

At a discrete valuation centered on the infinity chart of a nonexceptional component, with
`ν(1/s₁) = e > 0`, the resultant `Res(P₄, Z)` has order `-10e` (Lemma 8.3), `e = 2t` is even,
and the rank-five coordinate `J = N₀ Ψ` has order `-5t` (Corollary 8.4). The valuation may lie
over a singular point; only its center on this chart is used. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- At a discrete valuation centered on the infinity chart of a nonexceptional component, with
`ν(1/s₁) = e > 0`, the resultant has order `-10e`. -/
theorem nonexceptional_resultant_discrete_order
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (ha : a ≠ 0) (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (ν : AddValuation F (WithTop ℤ))
    (hregular : ∀ r : projectiveChart I ι (Ideal.Quotient.mk I (X 0)), 0 ≤ ν (r : F))
    {e : ℤ} (he : 0 < e)
    (hw : ν ((ι (Ideal.Quotient.mk I (X 0)))⁻¹) = (e : WithTop ℤ)) :
    ν (ι (Ideal.Quotient.mk I (curveResultant ρ u v ρ' u' v'))) =
      ((-10 * e : ℤ) : WithTop ℤ) := by
  have hl : ι (Ideal.Quotient.mk I (X 0)) ≠ 0 := by
    intro hz
    rw [hz, inv_zero, ν.map_zero] at hw
    exact WithTop.top_ne_coe hw
  exact chart_polynomial_discrete_order I ι _ hl ν hregular he hw _ 10
    (curveResultant_degree_le_ten _ _ _ _ _ _)
    (nonexceptional_chart_resultant_unit hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree)

/-- At a discrete valuation centered on the infinity chart of a nonexceptional component, with
`ν(1/s₁) = e > 0`, the multiplicity `e = 2t` is even and the rank-five coordinate `A Ψ` has
order `-5t`. -/
theorem nonexceptional_rank_five_discrete_order
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (hA : A ≠ 0) (ha : a ≠ 0) (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (ν : AddValuation F (WithTop ℤ))
    (hregular : ∀ r : projectiveChart I ι (Ideal.Quotient.mk I (X 0)), 0 ≤ ν (r : F))
    {e : ℤ} (he : 0 < e)
    (hw : ν ((ι (Ideal.Quotient.mk I (X 0)))⁻¹) = (e : WithTop ℤ)) :
    ∃ t : ℤ, 0 < t ∧ e = 2 * t ∧
      ν (ι (Ideal.Quotient.mk I (C A * curveNorm ρ u v ρ' u' v'))) =
        ((-5 * t : ℤ) : WithTop ℤ) := by
  let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
  have hc (c : ℚ) (hc : c ≠ 0) : ν (algebraMap ℚ F c) = 0 := by
    have hh := discrete_order_unit ν S.subtype hregular
      ((isUnit_iff_ne_zero.mpr hc).map (algebraMap ℚ S))
    change ν ((algebraMap ℚ S c : S) : F) = 0 at hh
    simpa only [Subalgebra.coe_algebraMap] using hh
  let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
  have hC (c : ℚ) : ψ (C c) = algebraMap ℚ F c := by
    exact ψ.commutes c
  have hrel : (algebraMap ℚ F A) * ψ (curveResultant ρ u v ρ' u' v') =
      (algebraMap ℚ F a) * ψ (curveNorm ρ u v ρ' u' v') ^ 4 := by
    have hz : ψ (curveEquation ρ u v ρ' u' v' A a) = 0 := by
      change ι (Ideal.Quotient.mk I _) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
    simpa only [curveEquation, map_sub, map_mul, map_pow, hC, sub_eq_zero] using hz
  have hres : ν (ψ (curveResultant ρ u v ρ' u' v')) = ((-10 * e : ℤ) : WithTop ℤ) :=
    nonexceptional_resultant_discrete_order hρ hu hv hne ρ' u' v' A a ha I hf hg
      ι hι hd hdegree ν hregular he hw
  have hD : ψ (curveNorm ρ u v ρ' u' v') ≠ 0 := by
    intro hz
    have hh := congrArg ν hrel
    simp only [hz, zero_pow (by decide : 4 ≠ 0), mul_zero, ν.map_zero,
      ν.map_mul, hc A hA, zero_add, hres] at hh
    exact WithTop.coe_ne_top hh
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((ν.ne_top_iff).mpr hD)
  have hh := congrArg ν hrel
  simp only [ν.map_mul, hc A hA, hc a ha, zero_add, ν.map_pow, ← hr, hres] at hh
  have heq : -10 * e = 4 * r := by exact_mod_cast hh
  refine ⟨e / 2, by omega, by omega, ?_⟩
  change ν (ψ (C A * curveNorm ρ u v ρ' u' v')) = _
  rw [map_mul, hC, ν.map_mul, hc A hA, zero_add, ← hr]
  congr 1
  omega

end
end PierceLengthBound.FixedDividend
