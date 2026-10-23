/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionSmoothSectionLocal
public import PierceLengthBound.PolarProjectionCenteredQuadric
public import PierceLengthBound.PolarProjectionBasePoint
public import PierceLengthBound.FixedDividendCurveEquations

/-! Explicit coordinates on sections through the polar base point. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial Matrix
noncomputable section

def polarSectionGapPolynomials {K : Type*} [CommRing K]
    (z : Fin 3 → K) (s t : K) : Fin 3 → MvPolynomial (Fin 2) K :=
  ![C (z 0) + X 1, C (z 1) + C s * X 0, C (z 2) + C t * X 0]

def polarSectionNodePolynomials {K : Type*} [CommRing K]
    (z : Fin 3 → K) (s t : K) : Fin 3 → MvPolynomial (Fin 2) K :=
  let x := polarSectionGapPolynomials z s t
  ![x 0, x 0 + x 1, x 0 + x 1 + x 2]

def polarSectionMap {K : Type*} [CommRing K] (z : Fin 3 → K) (s t : K) :
    MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval (polarSectionNodePolynomials z s t)

def polarSectionCoefficients {K : Type*} [CommRing K]
    (ρ u v ρ' u' v' s t : K) : Fin 5 → K :=
  let G := polarMatrix ρ u v
  let ℓ := polarLinear ρ u v ρ' u' v'
  ![G 0 0, -ℓ 0, 2 * G 0 1 * s + 2 * G 0 2 * t,
    -(ℓ 1 * s + ℓ 2 * t), G 1 1 * s ^ 2 + 2 * G 1 2 * s * t + G 2 2 * t ^ 2]

abbrev polarSectionIdeal {K : Type*} [CommRing K] (ρ u v ρ' u' v' s t : K) :=
  let c := polarSectionCoefficients ρ u v ρ' u' v' s t
  smoothSectionIdeal (c 0) (c 1) (c 2) (c 3) (c 4)

abbrev polarSectionPoint {K : Type*} [Field K] (ρ u v ρ' u' v' s t : K) :=
  let c := polarSectionCoefficients ρ u v ρ' u' v' s t
  smoothSectionPoint (c 0) (c 1) (c 2) (c 3) (c 4)

abbrev polarSectionBaseIdeal {K : Type*} [Field K] (ρ u v ρ' u' v' s t : K) :=
  let c := polarSectionCoefficients ρ u v ρ' u' v' s t
  smoothSectionBaseIdeal (c 0) (c 1) (c 2) (c 3) (c 4)

abbrev polarSectionLocalRing {K : Type*} [Field K] (ρ u v ρ' u' v' s t : K) :=
  Localization.AtPrime (polarSectionBaseIdeal ρ u v ρ' u' v' s t)

/-- The fixed-dividend equation in the local quadratic section. -/
def polarSectionLocalEquation {K : Type*} [Field K] (ρ u v ρ' u' v' A b s t : K) :
    polarSectionLocalRing ρ u v ρ' u' v' s t :=
  algebraMap _ _ (Ideal.Quotient.mk (polarSectionIdeal ρ u v ρ' u' v' s t)
    (polarSectionMap (polarBasePoint ρ u v ρ' u' v') s t
      (curveEquation ρ u v ρ' u' v' A b)))

/-- The original quadric becomes the explicit smooth quadratic section
under the centered coordinate substitution. -/
theorem polarSectionMap_quadric {K : Type*} [Field K]
    (ρ u v ρ' u' v' s t : K) (hG : (polarMatrix ρ u v).det ≠ 0) :
    let z := polarBasePoint ρ u v ρ' u' v'
    let c := polarSectionCoefficients ρ u v ρ' u' v' s t
    polarSectionMap z s t (curveQuadratic ρ u v ρ' u' v') =
      smoothSectionQuadric (c 0) (c 1) (c 2) (c 3) (c 4) := by
  let z := polarBasePoint ρ u v ρ' u' v'
  let w : Fin 3 → MvPolynomial (Fin 2) K := fun j => C (z j)
  let d : Fin 3 → MvPolynomial (Fin 2) K := ![X 1, C s * X 0, C t * X 0]
  have hw : polarVector (C ρ) (C u) (C v) (C ρ') (C u') (C v') w = 0 := by
    rw [← map_polarVector]
    simp [z, polarBasePoint_polarVector ρ u v ρ' u' v' hG]
    rfl
  have hquad := polar_centered_quadric_of_base (C ρ) (C u) (C v) (C ρ') (C u') (C v') w d hw
  rw [polarVector_dot_gaps] at hquad
  change polarSectionMap z s t _ = _
  have hleft : polarSectionMap z s t (curveQuadratic ρ u v ρ' u' v') =
      lineQuadratic (C ρ) (C u) (C v) (C ρ') (C u') (C v')
        ((w + d) 0) ((w + d) 0 + (w + d) 1)
        ((w + d) 0 + (w + d) 1 + (w + d) 2) := by
    change (polarSectionMap z s t).toRingHom
      (lineQuadratic (C ρ) (C u) (C v) (C ρ') (C u') (C v') (X 0) (X 1) (X 2)) = _
    rw [map_lineQuadratic]
    simp [polarSectionMap,
      polarSectionNodePolynomials, polarSectionGapPolynomials, w, d]
  rw [hleft, hquad]
  simp [polarCenteredQuadratic, polarCenteredLinear, polarSectionCoefficients,
    smoothSectionQuadric, polarMatrix, polarLinear, d, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, map_ofNat]
  ring

/-- Evaluating the section polynomial is the same as evaluating the
original polynomial along the full formal section. -/
theorem polarSectionMap_formal_eval {K : Type*} [CommRing K]
    (z : Fin 3 → K) (s t : K) (y : PowerSeries K) (p : MvPolynomial (Fin 3) K) :
    eval₂Hom PowerSeries.C ![PowerSeries.X, y] (polarSectionMap z s t p) =
      eval₂Hom PowerSeries.C
        (let x : Fin 3 → PowerSeries K :=
          ![PowerSeries.C (z 0) + y, PowerSeries.C (z 1) + PowerSeries.C s * PowerSeries.X,
            PowerSeries.C (z 2) + PowerSeries.C t * PowerSeries.X]
         ![x 0, x 0 + x 1, x 0 + x 1 + x 2]) p := by
  have he : (eval₂Hom PowerSeries.C ![PowerSeries.X, y]).comp
      (polarSectionMap z s t).toRingHom = eval₂Hom PowerSeries.C
        (let x : Fin 3 → PowerSeries K :=
          ![PowerSeries.C (z 0) + y, PowerSeries.C (z 1) + PowerSeries.C s * PowerSeries.X,
            PowerSeries.C (z 2) + PowerSeries.C t * PowerSeries.X]
         ![x 0, x 0 + x 1, x 0 + x 1 + x 2]) := by
    ext j
    · simp [polarSectionMap]
    · fin_cases j <;> simp [polarSectionMap, polarSectionNodePolynomials,
        polarSectionGapPolynomials]
  exact congrArg (fun h : MvPolynomial (Fin 3) K →+* PowerSeries K => h p) he

/-- The origin of the section is exactly the chosen base point in the
original cumulative-node coordinates. -/
theorem polarSectionMap_eval_origin {K : Type*} [CommRing K]
    (z : Fin 3 → K) (s t : K) (p : MvPolynomial (Fin 3) K) :
    eval (0 : Fin 2 → K) (polarSectionMap z s t p) =
      eval ![z 0, z 0 + z 1, z 0 + z 1 + z 2] p := by
  have he : (eval (0 : Fin 2 → K)).comp (polarSectionMap z s t).toRingHom =
      eval ![z 0, z 0 + z 1, z 0 + z 1 + z 2] := by
    ext j
    · simp [polarSectionMap]
    · fin_cases j <;> simp [polarSectionMap, polarSectionNodePolynomials,
        polarSectionGapPolynomials]
  exact congrArg (fun h : MvPolynomial (Fin 3) K →+* K => h p) he

/-- On the first axis hyperplane, the centered first and second gaps
recover every original coordinate. -/
theorem polar_first_axis_reconstruction {K D : Type*} [CommRing K] [CommRing D]
    [Algebra K D] (z : Fin 3 → K) (φ : MvPolynomial (Fin 3) K →ₐ[K] D)
    (hfixed : φ (X 2) - φ (X 1) = algebraMap K D (z 2)) :
    (aeval ![φ (X 1) - φ (X 0) - algebraMap K D (z 1),
      φ (X 0) - algebraMap K D (z 0)]).comp (polarSectionMap z 1 0) = φ := by
  ext j
  fin_cases j <;> simp [polarSectionMap, polarSectionNodePolynomials,
    polarSectionGapPolynomials]
  linear_combination -hfixed

/-- On the second axis hyperplane, the centered first and third gaps
recover every original coordinate. -/
theorem polar_second_axis_reconstruction {K D : Type*} [CommRing K] [CommRing D]
    [Algebra K D] (z : Fin 3 → K) (φ : MvPolynomial (Fin 3) K →ₐ[K] D)
    (hfixed : φ (X 1) - φ (X 0) = algebraMap K D (z 1)) :
    (aeval ![φ (X 2) - φ (X 1) - algebraMap K D (z 2),
      φ (X 0) - algebraMap K D (z 0)]).comp (polarSectionMap z 0 1) = φ := by
  ext j
  fin_cases j <;> simp [polarSectionMap, polarSectionNodePolynomials,
    polarSectionGapPolynomials]
  · linear_combination -hfixed
  · linear_combination -hfixed

end
end PierceLengthBound.FixedDividend
