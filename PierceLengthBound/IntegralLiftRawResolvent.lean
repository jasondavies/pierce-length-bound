/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftMoments
public import PierceLengthBound.IntegralLiftQuotientNormalization

/-! Explicit raw moment determinants and the actual rational resolvent identity. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial
set_option maxHeartbeats 1000000

lemma muF_X_four {a b i : ℕ} (hba : b < a) (hi : i + 4 < P a b) :
    muF a b i (X ^ 4) = kk a b i ^ 3 + 3 * kk a b i ^ 2 +
      3 * kk a b i * (kk a b (i + 1) + 1) +
      kk a b (i + 1) ^ 2 + 2 * kk a b (i + 1) + kk a b (i + 2) + 1 := by
  rw [show (X : Polynomial ℝ) ^ 4 = X * X ^ 3 by ring,
    muF_X_mul (by omega), pow_comp, X_comp, muF_shift_cube hba (by omega)]
  simp only [Nat.add_assoc]
  ring

lemma muF_shift_four {a b i : ℕ} (hba : b < a) (hi : i + 4 < P a b) (s : ℝ) :
    muF a b i ((X + C s) ^ 4) = s ^ 4 + 4 * s ^ 3 + 6 * s ^ 2 * (kk a b i + 1) +
      4 * s * (kk a b i ^ 2 + 2 * kk a b i + kk a b (i + 1) + 1) +
      kk a b i ^ 3 + 3 * kk a b i ^ 2 + 3 * kk a b i * (kk a b (i + 1) + 1) +
      kk a b (i + 1) ^ 2 + 2 * kk a b (i + 1) + kk a b (i + 2) + 1 := by
  rw [show (X + C s) ^ 4 = X ^ 4 + C (4 * s) * X ^ 3 + C (6 * s ^ 2) * X ^ 2 +
      C (4 * s ^ 3) * X + C (s ^ 4) by
        simp only [map_mul, map_pow, map_ofNat]; ring]
  simp only [muF_add, muF_C_mul, muF_C]
  rw [muF_X_four hba hi, muF_X_cube hba (by omega), muF_X_sq hba (by omega),
    muF_X hba (by omega), muF_one hba (by omega)]
  ring

lemma muF_X_five {a b i : ℕ} (hba : b < a) (hi : i + 5 < P a b) :
    muF a b i (X ^ 5) = kk a b i ^ 4 + 4 * kk a b i ^ 3 +
      6 * kk a b i ^ 2 * (kk a b (i + 1) + 1) +
      4 * kk a b i * (kk a b (i + 1) ^ 2 + 2 * kk a b (i + 1) + kk a b (i + 2) + 1) +
      kk a b (i + 1) ^ 3 + 3 * kk a b (i + 1) ^ 2 +
      3 * kk a b (i + 1) * (kk a b (i + 2) + 1) +
      kk a b (i + 2) ^ 2 + 2 * kk a b (i + 2) + kk a b (i + 3) + 1 := by
  rw [show (X : Polynomial ℝ) ^ 5 = X * X ^ 4 by ring,
    muF_X_mul (by omega), pow_comp, X_comp, muF_shift_four hba (by omega)]

lemma orbit_raw_hankelThree {a b i : ℕ} (hba : b < a) (hi : i + 4 < P a b) :
    hankelThree (fun j => muF a b i (X ^ j)) =
      rawHankelThree (kk a b i) (kk a b (i + 1)) (kk a b (i + 2)) := by
  unfold hankelThree
  simp only [pow_zero, pow_one]
  rw [muF_one hba (by omega), muF_X hba (by omega), muF_X_sq hba (by omega),
    muF_X_cube hba (by omega), muF_X_four hba hi]
  exact hankelThree_raw_identity _ _ _

lemma orbit_raw_hankelMixed {a b i : ℕ} (hba : b < a) (hi : i + 5 < P a b) :
    hankelMixed (fun j => muF a b i (X ^ j)) =
      rawHankelMixed (kk a b i) (kk a b (i + 1)) (kk a b (i + 2)) (kk a b (i + 3)) := by
  unfold hankelMixed
  simp only [pow_zero, pow_one]
  rw [muF_one hba (by omega), muF_X hba (by omega), muF_X_sq hba (by omega),
    muF_X_cube hba (by omega), muF_X_four hba (by omega), muF_X_five hba hi]
  exact hankelMixed_raw_identity _ _ _ _

/-- Actual resolvent, with both raw determinants given explicitly by gaps. -/
theorem orbit_integralLift_raw_resolvent {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    (integralLiftCoordinate a b i : ℝ) * (orbitQuartic a b i).eval (-(qq a b i : ℝ)) =
      (a : ℝ) * (((qq a b i : ℝ) - (orbitQuartic a b i).coeff 3) *
        rawHankelThree (kk a b i) (kk a b (i + 1)) (kk a b (i + 2)) -
        rawHankelMixed (kk a b i) (kk a b (i + 1)) (kk a b (i + 2)) (kk a b (i + 3))) := by
  rw [orbit_integralLift_resolvent hba hi, orbit_raw_hankelThree hba (by omega),
    orbit_raw_hankelMixed hba (by omega)]

def orbitNewtonQuarticQ (a b i : ℕ) : Polynomial ℚ :=
  firstNewtonQuartic
    (fun j : Fin 4 => coeffs (patternRhoQ a b i) (patternUQ a b i)
      (patternVQ a b i) j.castSucc)
    ![orbitFreeNodesQ a b i 0, orbitFreeNodesQ a b i 1, orbitFreeNodesQ a b i 2, 0]

lemma orbitNewtonQuarticQ_map (a b i : ℕ) :
    (orbitNewtonQuarticQ a b i).map (algebraMap ℚ ℝ) = orbitQuartic a b i := by
  rw [orbitQuartic_newton]
  simp [orbitNewtonQuarticQ, firstNewtonQuartic, coeffs, orbitCoeffs,
    patternRhoQ_cast, patternUQ_cast, patternVQ_cast, orbitFreeNodesQ_cast,
    orbitFreeNodes, patternRho, patternU, patternV]

/-- The actual raw resolvent also holds over the rational counting field. -/
theorem orbit_integralLift_raw_resolvent_Q {a b i : ℕ} (hba : b < a)
    (hi : i + 7 < P a b) :
    (integralLiftCoordinate a b i : ℚ) *
        (orbitNewtonQuarticQ a b i).eval (-(qq a b i : ℚ)) =
      (a : ℚ) * (((qq a b i : ℚ) - (orbitNewtonQuarticQ a b i).coeff 3) *
        rawHankelThree (kq a b i : ℚ) (kq a b (i + 1) : ℚ) (kq a b (i + 2) : ℚ) -
        rawHankelMixed (kq a b i : ℚ) (kq a b (i + 1) : ℚ)
          (kq a b (i + 2) : ℚ) (kq a b (i + 3) : ℚ)) := by
  have hv : (algebraMap ℚ ℝ) ((orbitNewtonQuarticQ a b i).eval (-(qq a b i : ℚ))) =
      (orbitQuartic a b i).eval (-(qq a b i : ℝ)) := by
    rw [← orbitNewtonQuarticQ_map]
    simpa using (eval_map_apply (p := orbitNewtonQuarticQ a b i)
      (algebraMap ℚ ℝ) (-(qq a b i : ℚ))).symm
  have hc : (algebraMap ℚ ℝ) ((orbitNewtonQuarticQ a b i).coeff 3) =
      (orbitQuartic a b i).coeff 3 := by
    rw [← orbitNewtonQuarticQ_map, coeff_map]
  apply (algebraMap ℚ ℝ).injective
  simp only [map_mul, map_sub, map_natCast]
  change (integralLiftCoordinate a b i : ℝ) *
    (algebraMap ℚ ℝ) ((orbitNewtonQuarticQ a b i).eval (-(qq a b i : ℚ))) = _
  rw [hv]
  have h := orbit_integralLift_raw_resolvent (i := i) hba (by omega)
  simpa only [rawHankelThree, rawHankelMixed, map_add, map_sub, map_mul,
    map_pow, map_one, map_ofNat, hc, kq, kk, Int.cast_sub, Int.cast_natCast, map_natCast] using h

end
end PierceLengthBound.FixedDividend
