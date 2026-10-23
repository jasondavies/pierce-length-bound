/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionCurveInitial
public import PierceLengthBound.PolarProjectionBaseMultiplicity

/-! First-order coefficients of the cubic norm and of the polar remainder along
formal sections through the rational certificate's base point, including their
higher-order terms. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial Matrix
noncomputable section

theorem polar_certificate_formal_norm_linear (x : Fin 3 → PowerSeries ℚ) (s t : ℚ)
    (hx0 : ∀ j, PowerSeries.constantCoeff (x j) = ![-1 / 7, -3 / 28, -1 / 2] j)
    (hx1 : ∀ j, PowerSeries.coeff 1 (x j) = ![(9 * s - 5 * t) / 4, s, t] j) :
    PowerSeries.coeff 1 (lineNorm
      (PowerSeries.C 2) (PowerSeries.C 5) (PowerSeries.C (-3))
      (PowerSeries.C 3) (PowerSeries.C 6) (PowerSeries.C (-5))
      (x 0) (x 0 + x 1) (x 0 + x 1 + x 2)) = polarCertificateNormLinear s t := by
  norm_num [lineNorm, lineNodes, extendedLineGaps, lineGaps, fourthNode, coeffs,
    Fin.sum_univ_succ, PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow,
    hx0, hx1, polarCertificateNormLinear, map_ofNat]
  ring

theorem polar_certificate_formal_remainder_linear (x : Fin 3 → PowerSeries ℚ) (s t : ℚ)
    (hx0 : ∀ j, PowerSeries.constantCoeff (x j) = ![-1 / 7, -3 / 28, -1 / 2] j)
    (hx1 : ∀ j, PowerSeries.coeff 1 (x j) = ![(9 * s - 5 * t) / 4, s, t] j) :
    let nodes := completeNodes (PowerSeries.C 2) (PowerSeries.C 5) (PowerSeries.C (-3))
      ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
    let rem := polarRemainderMonomialCoeffs
      (PowerSeries.C 2) (PowerSeries.C 5) (PowerSeries.C (-3))
      (PowerSeries.C 3) (PowerSeries.C 6) (PowerSeries.C (-5)) nodes
    polarCubic (fun j => PowerSeries.coeff 1 (rem j)) = polarCertificateRemainder s t := by
  dsimp only
  have htwo : PowerSeries.coeff 1 (2 : PowerSeries ℚ) = 0 := by
    rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from (map_ofNat PowerSeries.C 2).symm]
    simp
  have hthree : PowerSeries.coeff 1 (3 : PowerSeries ℚ) = 0 := by
    rw [show (3 : PowerSeries ℚ) = PowerSeries.C 3 from (map_ofNat PowerSeries.C 3).symm]
    simp
  have hr : (fun j => PowerSeries.coeff 1 (polarRemainderMonomialCoeffs
      (PowerSeries.C 2) (PowerSeries.C 5) (PowerSeries.C (-3))
      (PowerSeries.C 3) (PowerSeries.C 6) (PowerSeries.C (-5))
      (completeNodes (PowerSeries.C 2) (PowerSeries.C 5) (PowerSeries.C (-3))
        ![x 0, x 0 + x 1, x 0 + x 1 + x 2]) j)) =
      ![(77 * s + 7 * t) / 14, (-56 * s - 124 * t) / 14,
        (-45 * s + 157 * t) / 14, (28 * s - 28 * t) / 14] := by
    funext j
    fin_cases j <;>
      norm_num [polarRemainderMonomialCoeffs, polarRemainderCoefficients,
        polarQuotientConstant, completeNodes, fourthNode, PowerSeries.coeff_one_mul,
        PowerSeries.coeff_one_pow, hx0, hx1, map_ofNat, htwo, hthree] <;> ring
  rw [hr]
  rfl

end
end PierceLengthBound.FixedDividend
