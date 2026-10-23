/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionGoodSection
public import PierceLengthBound.PolarProjectionSectionCoordinates

/-! The good axis section has colength four in its actual algebraic local
ring. The proof uses the constructed formal section to determine the
algebraic section ideal, rather than assuming a completion comparison. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial Matrix
noncomputable section

theorem polarSectionMap_formal_eval_of_gap_form {K : Type*} [CommRing K]
    (z : Fin 3 → K) (s t : K) (x : Fin 3 → PowerSeries K)
    (hx1 : x 1 = PowerSeries.C (z 1) + PowerSeries.C s * PowerSeries.X)
    (hx2 : x 2 = PowerSeries.C (z 2) + PowerSeries.C t * PowerSeries.X)
    (p : MvPolynomial (Fin 3) K) :
    eval₂Hom PowerSeries.C ![PowerSeries.X, x 0 - PowerSeries.C (z 0)]
      (polarSectionMap z s t p) =
      eval₂Hom PowerSeries.C ![x 0, x 0 + x 1, x 0 + x 1 + x 2] p := by
  rw [polarSectionMap_formal_eval]
  have hgaps :
      ![PowerSeries.C (z 0) + (x 0 - PowerSeries.C (z 0)),
        PowerSeries.C (z 1) + PowerSeries.C s * PowerSeries.X,
        PowerSeries.C (z 2) + PowerSeries.C t * PowerSeries.X] = x := by
    funext j
    fin_cases j <;> simp [hx1, hx2]
  rw [hgaps]

/-- The formal coefficient calculation gives colength four in every model
of the actual local quadratic section. -/
theorem polar_formal_section_local_colength_four {S : Type*}
    (q : Fin 6 → ℚ) (hguard : polarChartGuard q ≠ 0) (A b s t : ℚ)
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra ℚ S]
    [Algebra (MvPolynomial (Fin 2) ℚ ⧸ polarSectionIdeal (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) s t) S]
    [IsScalarTower ℚ
      (MvPolynomial (Fin 2) ℚ ⧸ polarSectionIdeal (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) s t) S]
    [IsLocalization.AtPrime S (polarSectionBaseIdeal (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) s t)]
    (x : Fin 3 → PowerSeries ℚ)
    (hx0 : ∀ j, PowerSeries.constantCoeff (x j) =
      polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) j)
    (hq : lineQuadratic (PowerSeries.C (q 0)) (PowerSeries.C (q 1)) (PowerSeries.C (q 2))
      (PowerSeries.C (q 3)) (PowerSeries.C (q 4)) (PowerSeries.C (q 5))
      (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) = 0)
    (hx1 : x 1 = PowerSeries.C (polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) 1) +
      PowerSeries.C s * PowerSeries.X)
    (hx2 : x 2 = PowerSeries.C (polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) 2) +
      PowerSeries.C t * PowerSeries.X)
    (hcoeff :
      let E := eval ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
        (curveEquation (PowerSeries.C (q 0)) (PowerSeries.C (q 1)) (PowerSeries.C (q 2))
          (PowerSeries.C (q 3)) (PowerSeries.C (q 4)) (PowerSeries.C (q 5))
          (PowerSeries.C A) (PowerSeries.C b))
      (∀ j < 4, PowerSeries.coeff j E = 0) ∧ PowerSeries.coeff 4 E ≠ 0) :
    let J := polarSectionIdeal (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) s t
    let f := polarSectionMap (polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)) s t
      (curveEquation (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) A b)
    Module.Finite ℚ (S ⧸ Ideal.span {algebraMap _ S (Ideal.Quotient.mk J f)}) ∧
      Module.finrank ℚ (S ⧸ Ideal.span {algebraMap _ S (Ideal.Quotient.mk J f)}) = 4 := by
  let z := polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
  let c := polarSectionCoefficients (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) s t
  let y := x 0 - PowerSeries.C (z 0)
  let e := eval₂Hom PowerSeries.C ![PowerSeries.X, y]
  have hy0 : PowerSeries.constantCoeff y = 0 := by simp [y, z, hx0]
  obtain ⟨_, _, _, hG, _, hℓ⟩ := polarChartGuard_conditions hguard
  have hcb : c 1 ≠ 0 := neg_ne_zero.mpr hℓ
  have hqy : PowerSeries.C (c 0) * y ^ 2 +
      (PowerSeries.C (c 1) + PowerSeries.C (c 2) * PowerSeries.X) * y +
        PowerSeries.C (c 3) * PowerSeries.X + PowerSeries.C (c 4) * PowerSeries.X ^ 2 = 0 := by
    have he := congrArg e (polarSectionMap_quadric (q 0) (q 1) (q 2)
      (q 3) (q 4) (q 5) s t hG)
    change e (polarSectionMap z s t _) =
      e (smoothSectionQuadric (c 0) (c 1) (c 2) (c 3) (c 4)) at he
    rw [show e (polarSectionMap z s t _) = eval₂Hom PowerSeries.C
      ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
      (curveQuadratic (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)) from
        polarSectionMap_formal_eval_of_gap_form z s t x hx1 hx2 _] at he
    have hzq : eval₂Hom PowerSeries.C ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
        (curveQuadratic (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)) = 0 := by
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map,
        map_curveQuadratic, eval_curveQuadratic]
      exact hq
    rw [hzq] at he
    simpa [e, smoothSectionQuadric] using he.symm
  let f := polarSectionMap z s t (curveEquation (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) A b)
  have hf : e f = eval ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
      (curveEquation (PowerSeries.C (q 0)) (PowerSeries.C (q 1)) (PowerSeries.C (q 2))
        (PowerSeries.C (q 3)) (PowerSeries.C (q 4)) (PowerSeries.C (q 5))
        (PowerSeries.C A) (PowerSeries.C b)) := by
    rw [show e f = eval₂Hom PowerSeries.C ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
      (curveEquation (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) A b) from
        polarSectionMap_formal_eval_of_gap_form z s t x hx1 hx2 _]
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map, map_curveEquation]
  dsimp only at hcoeff
  exact smoothSection_local_colength (R := S) (c 0) (c 1) (c 2) (c 3) (c 4) hcb y hy0 hqy f 4
    (by rw [← hf] at hcoeff; exact hcoeff.1) (by rw [← hf] at hcoeff; exact hcoeff.2)

/-- Outside the proper exceptional polynomial, one of the two coordinate
axis sections has algebraic local colength four, for every dividend. -/
theorem polar_good_axis_local_colength_four (q : Fin 6 → ℚ)
    (hguard : polarChartGuard q ≠ 0) (hminor : polarInitialMinor q ≠ 0)
    (A b : ℚ) (hA : A ≠ 0) :
    ∃ s t : ℚ, ((s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1)) ∧
      let S := polarSectionLocalRing (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) s t
      let _ : CommRing S := inferInstance
      let f : S := polarSectionLocalEquation (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) A b s t
      Module.Finite ℚ (S ⧸ Ideal.span {f}) ∧ Module.finrank ℚ (S ⧸ Ideal.span {f}) = 4 := by
  obtain ⟨s, t, x, haxis, hx0, _, hq, hx1, hx2, hcoeff⟩ :=
    polar_good_axis_formal_section q hguard hminor A b hA
  refine ⟨s, t, haxis, ?_⟩
  exact polar_formal_section_local_colength_four
    (S := polarSectionLocalRing (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) s t)
    q hguard A b s t x hx0 hq hx1 hx2 hcoeff

end
end PierceLengthBound.FixedDividend
