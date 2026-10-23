/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionCenteredQuadric
public import PierceLengthBound.PolarProjectionInitialForm
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-! Smooth formal sections of the quadric through its polar base point.
The section is constructed by Hensel lifting; it is not assumed as input. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial Matrix
noncomputable section

/-- A quadratic with a simple root at the origin of the residue field has
a formal root with zero constant coefficient. -/
theorem formal_monic_quadratic_root {K : Type*} [Field K]
    (b c : PowerSeries K) (hb : PowerSeries.constantCoeff b ≠ 0)
    (hc : PowerSeries.constantCoeff c = 0) :
    ∃ y : PowerSeries K, PowerSeries.constantCoeff y = 0 ∧ y ^ 2 + b * y + c = 0 := by
  let I : Ideal (PowerSeries K) := Ideal.span {PowerSeries.X}
  let f : Polynomial (PowerSeries K) := X ^ 2 + C b * X + C c
  have hf : f.Monic := by
    dsimp only [f]
    rw [add_assoc]
    apply Polynomial.monic_X_pow_add
    compute_degree
    norm_num
  have hf0 : f.eval 0 ∈ I := by
    simp only [f, eval_add, eval_pow, eval_X, eval_mul, eval_C, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_add]
    exact Ideal.mem_span_singleton.mpr (PowerSeries.X_dvd_iff.mpr hc)
  have hbunit : IsUnit b := PowerSeries.isUnit_iff_constantCoeff.mpr
    (isUnit_iff_ne_zero.mpr hb)
  have hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 0)) := by
    simpa [f] using hbunit.map (Ideal.Quotient.mk I)
  obtain ⟨y, hy, hyI⟩ := HenselianRing.is_henselian (I := I) f hf 0 hf0 hderiv
  refine ⟨y, ?_, ?_⟩
  · apply PowerSeries.X_dvd_iff.mp
    exact Ideal.mem_span_singleton.mp (by simpa using hyI)
  · simpa [Polynomial.IsRoot, f] using hy

/-- The same lifting statement without normalizing the nonzero quadratic coefficient. -/
theorem formal_quadratic_root {K : Type*} [Field K]
    (a : K) (ha : a ≠ 0) (b c : PowerSeries K)
    (hb : PowerSeries.constantCoeff b ≠ 0) (hc : PowerSeries.constantCoeff c = 0) :
    ∃ y : PowerSeries K, PowerSeries.constantCoeff y = 0 ∧
      PowerSeries.C a * y ^ 2 + b * y + c = 0 := by
  have hu : PowerSeries.C a * PowerSeries.C a⁻¹ = (1 : PowerSeries K) := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  obtain ⟨y, hy0, hy⟩ := formal_monic_quadratic_root
    (PowerSeries.C a⁻¹ * b) (PowerSeries.C a⁻¹ * c)
    (by simpa using mul_ne_zero (inv_ne_zero ha) hb) (by simp [hc])
  refine ⟨y, hy0, ?_⟩
  have he := congrArg (fun t => PowerSeries.C a * t) hy
  simpa only [mul_add, ← mul_assoc, hu, one_mul, mul_zero] using he

/-- The fixed tangent direction in the chart where the first linear
coefficient is nonzero. -/
def polarTangentDirection {K : Type*} [Field K]
    (ρ u v ρ' u' v' s t : K) : Fin 3 → K :=
  let ℓ := polarLinear ρ u v ρ' u' v'
  ![-(ℓ 1 * s + ℓ 2 * t) / ℓ 0, s, t]

/-- A formal section of the smooth quadric exists in every tangent direction
in the first-coordinate chart. Its higher terms are constructed by Hensel lifting. -/
theorem exists_polar_formal_section {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K) (hG : (polarMatrix ρ u v).det ≠ 0)
    (h00 : polarMatrix ρ u v 0 0 ≠ 0)
    (hℓ : polarLinear ρ u v ρ' u' v' 0 ≠ 0) (s t : K) :
    ∃ x : Fin 3 → PowerSeries K,
      (∀ j, PowerSeries.constantCoeff (x j) = polarBasePoint ρ u v ρ' u' v' j) ∧
      (∀ j, PowerSeries.coeff 1 (x j) = polarTangentDirection ρ u v ρ' u' v' s t j) ∧
      lineQuadratic (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
        (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v')
        (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) = 0 ∧
      x 1 = PowerSeries.C (polarBasePoint ρ u v ρ' u' v' 1) + PowerSeries.C s * PowerSeries.X ∧
      x 2 = PowerSeries.C (polarBasePoint ρ u v ρ' u' v' 2) + PowerSeries.C t * PowerSeries.X := by
  let G := polarMatrix ρ u v
  let ℓ := polarLinear ρ u v ρ' u' v'
  let b : PowerSeries K :=
    PowerSeries.C (2 * G 0 1 * s + 2 * G 0 2 * t) * PowerSeries.X - PowerSeries.C (ℓ 0)
  let c : PowerSeries K :=
    PowerSeries.C (G 1 1 * s ^ 2 + 2 * G 1 2 * s * t + G 2 2 * t ^ 2) * PowerSeries.X ^ 2 -
      PowerSeries.C (ℓ 1 * s + ℓ 2 * t) * PowerSeries.X
  obtain ⟨y, hy0, hy⟩ := formal_quadratic_root (G 0 0) h00 b c
    (by simpa [b] using neg_ne_zero.mpr hℓ) (by simp [c])
  have hy1 : PowerSeries.coeff 1 y = -(ℓ 1 * s + ℓ 2 * t) / ℓ 0 := by
    have he := congrArg (PowerSeries.coeff 1) hy
    simp [b, c, PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow, hy0] at he
    field_simp [show ℓ 0 ≠ 0 from hℓ]
    linear_combination -he
  let z : Fin 3 → PowerSeries K := fun j => PowerSeries.C (polarBasePoint ρ u v ρ' u' v' j)
  let d : Fin 3 → PowerSeries K := ![y, PowerSeries.C s * PowerSeries.X,
    PowerSeries.C t * PowerSeries.X]
  have hz : polarVector (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
      (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v') z = 0 := by
    rw [← map_polarVector]
    simp [polarBasePoint_polarVector ρ u v ρ' u' v' hG]
    rfl
  have hcenter : polarCenteredQuadratic (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v) d -
      polarCenteredLinear (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
        (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v') d = 0 := by
    have he : polarCenteredQuadratic (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v) d -
        polarCenteredLinear (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
          (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v') d =
        PowerSeries.C (G 0 0) * y ^ 2 + b * y + c := by
      simp [polarCenteredQuadratic, polarCenteredLinear, polarMatrix, polarLinear,
        d, b, c, G, ℓ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, map_ofNat]
      ring
    exact he.trans hy
  refine ⟨z + d, ?_, ?_, ?_, rfl, rfl⟩
  · intro j
    fin_cases j <;> simp [z, d, hy0]
  · intro j
    fin_cases j <;> simp [z, d, polarTangentDirection, hy1, ℓ]
  · rw [← polarVector_dot_gaps,
      polar_centered_quadric_of_base _ _ _ _ _ _ z d hz]
    exact hcenter

end
end PierceLengthBound.FixedDividend
