/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionAlgebra
public import PierceLengthBound.FixedDividendCoordinates

/-! The affine polar identity at supported Pierce orbit states. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Matrix Finset
noncomputable section

/-- The polar direction evaluated at the actual first three gaps. -/
def orbitPolarVector (a b i : ℕ) : Fin 3 → ℝ :=
  polarVector (patternRho a b i) (patternU a b i) (patternV a b i)
    (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
    (fun j => kk a b (i + j))

lemma orbit_kernel_drops {a b i : ℕ} (hba : b < a) (hi : i + 5 < P a b) :
    -patternRho a b i * (dq a b i : ℝ) + patternU a b i * (dq a b (i + 1) : ℝ) +
      patternV a b i * (dq a b (i + 2) : ℝ) + (dq a b (i + 3) : ℝ) = 0 := by
  have hL := orbit_label_ne_zero hba hi
  have he : -Lz a b (i + 1) * dq a b i + U1z a b i * dq a b (i + 1) +
      U2z a b i * dq a b (i + 2) + Lz a b i * dq a b (i + 3) = 0 :=
    null_d _ _ _ _ _ _ _ _ _
  have heR : -(Lz a b (i + 1) : ℝ) * (dq a b i : ℝ) +
      (U1z a b i : ℝ) * (dq a b (i + 1) : ℝ) +
      (U2z a b i : ℝ) * (dq a b (i + 2) : ℝ) +
      (Lz a b i : ℝ) * (dq a b (i + 3) : ℝ) = 0 := by exact_mod_cast he
  simp only [patternRho, patternU, patternV]
  field_simp
  linear_combination heR

lemma orbit_drop_fourthNode {a b i : ℕ} (hba : b < a) (hi : i + 5 < P a b) :
    fourthNode (patternRho a b i) (patternU a b i) (patternV a b i)
      (dq a b i : ℝ) (dq a b i + dq a b (i + 1))
      (dq a b i + dq a b (i + 1) + dq a b (i + 2)) =
        (orb a b i : ℝ) - orb a b (i + 4) := by
  have he := orbit_kernel_drops hba hi
  simp only [fourthNode, dq, Int.cast_sub, Int.cast_natCast] at he ⊢
  linear_combination -he

lemma orbit_lineDropGaps {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    lineGaps (patternRho a b i) (patternU a b i) (patternV a b i)
      (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
      (dq a b i : ℝ) (dq a b i + dq a b (i + 1))
      (dq a b i + dq a b (i + 1) + dq a b (i + 2)) =
        fun j : Fin 5 => (dq a b (i + j) : ℝ) := by
  have he := orbit_kernel_drops hba (by omega : i + 1 + 5 < P a b)
  simp only [Nat.add_assoc] at he
  unfold lineGaps
  rw [orbit_drop_fourthNode hba (by omega)]
  funext j
  fin_cases j <;> simp only [dq, Int.cast_sub, Int.cast_natCast, Nat.add_assoc,
    Nat.add_zero, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val] at he ⊢
  all_goals first | (solve | ring) | linear_combination -he

lemma orbit_lineDropNodes {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    lineNodes (patternRho a b i) (patternU a b i) (patternV a b i)
      (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
      (dq a b i : ℝ) (dq a b i + dq a b (i + 1))
      (dq a b i + dq a b (i + 1) + dq a b (i + 2)) =
        fun j : Fin 6 => (orb a b i : ℝ) - orb a b (i + j) := by
  unfold lineNodes
  rw [orbit_drop_fourthNode hba (by omega), orbit_lineDropGaps hba hi]
  funext j
  fin_cases j <;> simp [dq, Nat.add_assoc]

lemma orbit_gap_nodes (a b i : ℕ) :
    kk a b i = pt a b i 1 ∧
      kk a b i + kk a b (i + 1) = pt a b i 2 ∧
      kk a b i + kk a b (i + 1) + kk a b (i + 2) = pt a b i 3 := by
  simp [kk, pt, Nat.add_assoc]

/-- The polar direction is orthogonal to the actual gap row. -/
theorem orbitPolarVector_dot_gaps {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    ∑ j : Fin 3, kk a b (i + j) * orbitPolarVector a b i j = 0 := by
  rw [orbitPolarVector, polarVector_dot_gaps]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero]
  rw [(orbit_gap_nodes a b i).2.2, (orbit_gap_nodes a b i).2.1,
    (orbit_gap_nodes a b i).1]
  exact orbit_lineQuadratic_zero hba hi

/-- The cofactor relation for the actual orbit values, with denominators removed. -/
lemma orbitCoeffs_values_sum {a b i : ℕ} (hba : b < a) (hi : i + 5 < P a b) :
    ∑ j : Fin 5, orbitCoeffs a b i j * (orb a b (i + j) : ℝ) = 0 := by
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have he := congrArg (fun t : ℝ => t * a) (orbitCoeffs_weighted_moment hba hi)
  simp only [Finset.sum_mul, mul_assoc, div_mul_cancel₀ _ ha, zero_mul] at he
  exact he

/-- The orbit recurrence turns the cofactor relation into a polarized moment identity. -/
lemma orbit_mixed_drop_moment {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    ∑ j : Fin 5, orbitCoeffs a b i j *
      (pt a b i j * ((orb a b i : ℝ) - orb a b (i + j)) + (dq a b (i + j) : ℝ)) = 0 := by
  have hB := orbitCoeffs_values_sum hba (by omega : i + 5 < P a b)
  have hs := orbitCoeffs_first_moment hba (by omega : i + 5 < P a b)
  have hrec : (∑ j : Fin 5, orbitCoeffs a b i j *
      (((qq a b i : ℝ) + pt a b i j) * (orb a b (i + j) : ℝ) +
        orb a b (i + j + 1))) = 0 := by
    have he (j : Fin 5) :
        ((qq a b i : ℝ) + pt a b i j) * (orb a b (i + j) : ℝ) +
          orb a b (i + j + 1) = a := by
      have hj : i + j < P a b := by have := j.isLt; omega
      have h : (orb a b (i + j) : ℝ) * qq a b (i + j) +
          orb a b (i + j + 1) = a := by exact_mod_cast orb_div hj
      dsimp only [pt]
      linear_combination h
    simp_rw [he]
    rw [← Finset.sum_mul, orbitCoeffs_sum, zero_mul]
  calc
    _ = (orb a b i : ℝ) * (∑ j : Fin 5, orbitCoeffs a b i j * pt a b i j) +
        ((qq a b i : ℝ) + 1) *
          (∑ j : Fin 5, orbitCoeffs a b i j * (orb a b (i + j) : ℝ)) -
        (∑ j : Fin 5, orbitCoeffs a b i j *
          (((qq a b i : ℝ) + pt a b i j) * (orb a b (i + j) : ℝ) +
            orb a b (i + j + 1))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [dq, Int.cast_sub, Int.cast_natCast]
      ring
    _ = 0 := by rw [hs, hB, hrec]; ring

/-- The polar direction annihilates the actual drop row. -/
theorem orbitPolarVector_dot_drops {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    ∑ j : Fin 3, (dq a b (i + j) : ℝ) * orbitPolarVector a b i j = 0 := by
  unfold orbitPolarVector
  rw [polarVector_dot_row]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero]
  rw [(orbit_gap_nodes a b i).2.2, (orbit_gap_nodes a b i).2.1,
    (orbit_gap_nodes a b i).1, orbit_lineNodes hba hi,
    orbit_lineDropNodes hba hi, orbit_lineDropGaps hba hi]
  exact orbit_mixed_drop_moment hba hi

/-- The polar direction pairs with the actual quadratic-moment row to give the norm. -/
theorem orbitPolarVector_dot_moment {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    ∑ j : Fin 3, orbitPolarVector a b i j * (rq a b i j : ℝ) = orbitNorm a b i := by
  have he := polarVector_dot_moment_sub_norm
    (patternRho a b i) (patternU a b i) (patternV a b i)
    (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
    (fun j : Fin 3 => kk a b (i + j))
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero] at he
  rw [(orbit_gap_nodes a b i).2.2, (orbit_gap_nodes a b i).2.1,
    (orbit_gap_nodes a b i).1, orbit_lineQuadratic_zero hba hi, mul_zero,
    orbit_lineNorm_eq hba hi, orbit_lineGaps hba hi, orbit_lineNodes hba hi] at he
  apply sub_eq_zero.mp
  simpa only [orbitPolarVector, rq, sq, kq, Int.cast_add, Int.cast_mul,
    Int.cast_sub, Int.cast_natCast, Fin.val_castSucc, Fin.val_succ, kk, pt, Nat.add_assoc] using he

/-- The exact polar identity `D W = A (G x + ℓ)` at every supported actual state. -/
theorem orbit_polar_identity {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) (j : Fin 3) :
    orbitNorm a b i * (orbitCurvatureVector a b i j : ℝ) =
      (Lz a b i : ℝ) * orbitPolarVector a b i j := by
  have he := polar_curvature_scalar_identity
    (fun j : Fin 3 => (dq a b (i + j) : ℝ))
    (fun j : Fin 3 => kk a b (i + j))
    (fun j : Fin 3 => (rq a b i j : ℝ)) (orbitPolarVector a b i)
    (orbitPolarVector_dot_drops hba hi) (orbitPolarVector_dot_gaps hba hi) j
  rw [orbitPolarVector_dot_moment hba hi] at he
  have hdet : (Matrix.of ![fun j : Fin 3 => (dq a b (i + j) : ℝ),
      fun j : Fin 3 => kk a b (i + j), fun j : Fin 3 => (rq a b i j : ℝ)]).det = Lz a b i := by
    have h := orbitCurvature_dot_r a b i
    rw [orbitCurvatureVector, curvature_dot_row] at h
    have hR := congrArg (fun z : ℤ => (z : ℝ)) h
    simpa [Matrix.det_fin_three, kq, kk] using hR
  rw [hdet] at he
  convert he using 1
  congr 1
  fin_cases j <;> simp [orbitCurvatureVector, curvatureVector, kk, kq]

/-- Clearing the positive norm gives `J W = A² (G x + ℓ)`. -/
theorem orbit_rankFive_polar_identity {a b i : ℕ} (hba : b < a)
    (hi : i + 7 < P a b) (j : Fin 3) :
    hankelInv a b i 5 * (orbitCurvatureVector a b i j : ℝ) =
      (Lz a b i : ℝ) ^ 2 * orbitPolarVector a b i j := by
  rw [← joint_rank_five_identity hba hi]
  linear_combination (Lz a b i : ℝ) * orbit_polar_identity (i := i) hba (by omega) j

end
end PierceLengthBound.FixedDividend
