/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FunctionParameterChange
public import PierceLengthBound.JointLiftCurvatureNonvanishing

/-! The curvature combination giving the extra finite zero is a transcendental
function, so it can serve as a parameter in the zero/pole fiber comparison. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

theorem orbitJoint_exists_transcendental_curvature_combination {a b i d : ℕ}
    (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (F : MvPolynomial (Fin 3) ℚ) (hF : Prime F) (hFdeg : F.totalDegree = 2) (hFI : F ∈ I)
    (hd3 : 3 ≤ d)
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    let W := fun j : Fin 3 => jointGraphMap I (orbitJointNumerators a b i)
      (orbitJointDenominator a b i) (X (Sum.inr j.castSucc))
    let φ := graphPointMap I (orbitJointDenominator a b i) (orbitFreeNodesQ a b i)
      hz (orbitJointDenominator_eval_ne_zero hba hi)
    ∃ v : Fin 3 → ℚ, Transcendental ℚ (∑ j, algebraMap ℚ _ (v j) * W j) ∧
      φ (∑ j, algebraMap ℚ _ (v j) * W j) = 0 := by
  have hD : orbitJointDenominator a b i ∉ I := fun h =>
    orbitJointDenominator_eval_ne_zero hba hi (hz _ h)
  have hD0 : Ideal.Quotient.mk I (orbitJointDenominator a b i) ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hD
  let : IsDomain (graphLocalization I (orbitJointDenominator a b i)) :=
    Localization.Away.isDomain hD0
  obtain ⟨v, hv, hzero⟩ := orbitJoint_exists_curvature_combination_vanishing
    hba hi I hz F hF hFdeg hFI hd3 hd
  exact ⟨v, transcendental_of_nonzero_point_zero _ hv hzero, hzero⟩

end
end PierceLengthBound.FixedDividend
