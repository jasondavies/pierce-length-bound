/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftQuotientOrder
public import PierceLengthBound.FixedDividendRationalChartResultant
public import PierceLengthBound.FixedDividendChartGeneration

/-! Valuations centered on the actual infinity chart. Units modulo the infinity
equation have order zero, and homogenization converts this into exact pole orders. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

variable {R K : Type*} [CommRing R] [Field K]

lemma discrete_order_unit (v : AddValuation K (WithTop ℤ)) (φ : R →+* K)
    (hregular : ∀ r, 0 ≤ v (φ r)) {r : R} (hr : IsUnit r) : v (φ r) = 0 := by
  obtain ⟨s, hs, _⟩ := isUnit_iff_exists.mp hr
  have hv : v (φ r) + v (φ s) = 0 := by
    rw [← v.map_mul, ← map_mul, hs, map_one, v.map_one]
  exact le_antisymm ((le_add_of_nonneg_right (hregular s)).trans hv.le) (hregular r)

/-- A valuation nonnegative on a K-algebra chart is trivial on its nonzero
constant field: both a constant and its inverse belong to the chart. -/
lemma chart_constant_discrete_order {F : Type*} [Field F] [Algebra K F]
    (S : Subalgebra K F) (v : AddValuation F (WithTop ℤ))
    (hregular : ∀ r : S, 0 ≤ v (r : F)) {c : K} (hc : c ≠ 0) :
    v (algebraMap K F c) = 0 := by
  have hh := discrete_order_unit v S.subtype hregular
    ((isUnit_iff_ne_zero.mpr hc).map (algebraMap K S))
  change v ((algebraMap K S c : S) : F) = 0 at hh
  simpa only [Subalgebra.coe_algebraMap] using hh

/-- A unit on the infinity section stays a unit at any valuation centered on
that section, including valuations over singular points. -/
theorem discrete_order_unit_mod_infinity (v : AddValuation K (WithTop ℤ))
    (φ : R →+* K) (hregular : ∀ r, 0 ≤ v (φ r)) {w r : R}
    (hw : 0 < v (φ w))
    (hr : IsUnit (Ideal.Quotient.mk (Ideal.span {w}) r)) : v (φ r) = 0 := by
  obtain ⟨s', hs', _⟩ := isUnit_iff_exists.mp hr
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
  have hm : r * s - 1 ∈ Ideal.span {w} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_sub, map_mul, map_one, sub_eq_zero] using hs'
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hm
  have hpos : 0 < v (φ (r * s) - 1) := by
    rw [← map_one φ, ← map_sub, hu, map_mul, v.map_mul]
    exact lt_of_lt_of_le hw (le_add_of_nonneg_right (hregular u))
  have hzero : v (φ (r * s)) = 0 := by
    have hh := v.map_eq_of_lt_sub (x := 1) (y := φ (r * s)) (by simpa using hpos)
    simpa using hh
  rw [map_mul, v.map_mul] at hzero
  exact le_antisymm ((le_add_of_nonneg_right (hregular s)).trans hzero.le) (hregular r)

/-- Every degree-at-most-n polynomial has pole order at most n times the
original infinity order. This also covers the zero function. -/
theorem chart_polynomial_discrete_order_ge {F : Type*} [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K))
    (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (hl : ι l ≠ 0)
    (v : AddValuation F (WithTop ℤ))
    (hregular : ∀ r : projectiveChart I ι l, 0 ≤ v (r : F))
    {e : ℤ} (hw : v ((ι l)⁻¹) = (e : WithTop ℤ))
    (f : MvPolynomial (Fin 3) K) (n : ℕ) (hdeg : f.totalDegree ≤ n) :
    ((-(n : ℤ) * e : ℤ) : WithTop ℤ) ≤ v (ι (Ideal.Quotient.mk I f)) := by
  have hz := hregular (chartHomogeneousMap I ι l (curveHomogenize n f))
  rw [chartHomogeneousMap_homogenize_value I ι l hl f hdeg, v.map_mul,
    discrete_order_pow v hw n] at hz
  by_cases htop : v (ι (Ideal.Quotient.mk I f)) = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
  rw [← hr] at hz ⊢
  have heq : 0 ≤ r + (n : ℤ) * e := by exact_mod_cast hz
  exact_mod_cast (show -(n : ℤ) * e ≤ r by nlinarith)

/-- A homogeneous polynomial that is a unit modulo infinity has exactly its
homogeneous degree times the chart pole order in the original affine variables. -/
theorem chart_polynomial_discrete_order {F : Type*} [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K))
    (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (hl : ι l ≠ 0)
    (v : AddValuation F (WithTop ℤ))
    (hregular : ∀ r : projectiveChart I ι l, 0 ≤ v (r : F))
    {e : ℤ} (he : 0 < e) (hw : v ((ι l)⁻¹) = (e : WithTop ℤ))
    (f : MvPolynomial (Fin 3) K) (n : ℕ) (hdeg : f.totalDegree ≤ n)
    (hunit : IsUnit (Ideal.Quotient.mk (chartInfinityIdeal I ι l)
      (chartHomogeneousMap I ι l (curveHomogenize n f)))) :
    v (ι (Ideal.Quotient.mk I f)) = ((-(n : ℤ) * e : ℤ) : WithTop ℤ) := by
  have hz := discrete_order_unit_mod_infinity v (projectiveChart I ι l).subtype
    hregular (w := chartInfinityCoordinate I ι l)
    (r := chartHomogeneousMap I ι l (curveHomogenize n f))
    (by change 0 < v ((ι l)⁻¹); rw [hw]; exact_mod_cast he) hunit
  change v ((chartHomogeneousMap I ι l (curveHomogenize n f) : F)) = 0 at hz
  rw [chartHomogeneousMap_homogenize_value I ι l hl f hdeg, v.map_mul,
    discrete_order_pow v hw n] at hz
  have hf0 : ι (Ideal.Quotient.mk I f) ≠ 0 := by
    intro hf
    rw [hf, v.map_zero, top_add] at hz
    exact WithTop.top_ne_coe hz
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hf0)
  rw [← hr] at hz ⊢
  have heq : r + (n : ℤ) * e = 0 := by exact_mod_cast hz
  congr 1
  linear_combination heq

end
end PierceLengthBound.FixedDividend
