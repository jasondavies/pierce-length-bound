/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendConicPatternCoefficients
public import PierceLengthBound.FixedDividendSecondParabolicModel
public import PierceLengthBound.FixedDividendConicPlanePivot

/-! The actual rational plane models equal their explicitly cleared forms. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

lemma first_conic_ternary_representation
    (r u v r' u' v' D n0 n1 n2 e : ℤ) (hD : D ≠ 0) :
    let w := ternaryNumerators r u v r' u' v' D
    rationalPlaneConicCoefficients ((r : ℚ) / D) ((u : ℚ) / D) ((v : ℚ) / D)
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) n0 n1 n2 e =
    planeConicCoefficients ((w 0 : ℚ) / D) ((w 1 : ℚ) / D) ((w 2 : ℚ) / D)
      ((w 3 : ℚ) / D ^ 2) ((w 4 : ℚ) / D ^ 2) ((w 5 : ℚ) / D ^ 2)
      (-(n0 : ℚ) / n2) (-(n1 : ℚ) / n2) (-(e : ℚ) / n2) := by
  have hh := congrArg (fun w : Fin 6 → ℚ =>
    planeConicCoefficients (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
      (-(n0 : ℚ) / n2) (-(n1 : ℚ) / n2) (-(e : ℚ) / n2))
    (ternaryNumerators_rat r u v r' u' v' D hD)
  exact hh.symm

lemma second_conic_ternary_representation
    (r u v r' u' v' D n0 n1 n2 e : ℤ) (hD : D ≠ 0) :
    let w := ternaryNumerators r u v r' u' v' D
    rationalSecondPlaneConicCoefficients ((r : ℚ) / D) ((u : ℚ) / D) ((v : ℚ) / D)
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) n0 n1 n2 e =
    planeConicCoefficients ((w 0 : ℚ) / D) ((w 2 : ℚ) / D) ((w 1 : ℚ) / D)
      ((w 3 : ℚ) / D ^ 2) ((w 5 : ℚ) / D ^ 2) ((w 4 : ℚ) / D ^ 2)
      (-(n0 : ℚ) / n1) (-(n2 : ℚ) / n1) (-(e : ℚ) / n1) := by
  have hh := congrArg (fun w : Fin 6 → ℚ =>
    planeConicCoefficients (w 0) (w 2) (w 1) (w 3) (w 5) (w 4)
      (-(n0 : ℚ) / n1) (-(n2 : ℚ) / n1) (-(e : ℚ) / n1))
    (ternaryNumerators_rat r u v r' u' v' D hD)
  exact hh.symm

end
end PierceLengthBound.FixedDividend
