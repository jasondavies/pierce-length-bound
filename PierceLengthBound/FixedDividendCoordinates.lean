/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendGapExclusion
public import PierceLengthBound.FixedDividendLineResultant

/-!
# Coordinates of the actual orbit quartics

These bridges identify the orbit polynomials with the explicit Newton forms used
in the universal resultant certificates.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

open Finset Polynomial

variable {a b : ℕ}

noncomputable def patternRho (a b i : ℕ) : ℝ := (Lz a b (i + 1) : ℝ) / Lz a b i
noncomputable def patternU (a b i : ℕ) : ℝ := (U1z a b i : ℝ) / Lz a b i
noncomputable def patternV (a b i : ℕ) : ℝ := (U2z a b i : ℝ) / Lz a b i

lemma orbitCoeffs_eq (i : ℕ) :
    orbitCoeffs a b i = coeffs (patternRho a b i) (patternU a b i) (patternV a b i) := rfl

theorem orbit_pattern_signs (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    0 < patternRho a b i ∧ 0 < patternU a b i ∧ patternV a b i < 0 := by
  have hA := Lz_pos hba (by omega : i + 5 < P a b)
  have hA' := Lz_pos hba (by omega : i + 1 + 5 < P a b)
  have hsign := pattern_signs hA hA'
    (kq_pos (by omega)) (kq_pos (by omega)) (kq_pos (by omega))
    (kq_pos (by omega)) (kq_pos (by omega)) (e0_at i) (e3_at i)
  have hA0 : (0 : ℝ) < Lz a b i := by exact_mod_cast (by omega : (0 : ℤ) < Lz a b i)
  have hA1 : (0 : ℝ) < Lz a b (i + 1) := by
    exact_mod_cast (by omega : (0 : ℤ) < Lz a b (i + 1))
  have hU : (0 : ℝ) < U1z a b i := by exact_mod_cast hsign.1
  have hV : (U2z a b i : ℝ) < 0 := by exact_mod_cast hsign.2
  exact ⟨div_pos hA1 hA0, div_pos hU hA0, div_neg_of_neg_of_pos hV hA0⟩

/-- Actual first quartic in the explicit Newton coordinates. -/
theorem orbitQuartic_newton (i : ℕ) :
    orbitQuartic a b i = firstNewtonQuartic
      (fun j : Fin 4 => orbitCoeffs a b i j.castSucc)
      (fun j : Fin 4 => pt a b i ((j : ℕ) + 1)) := by
  simp [orbitQuartic, newtonQuartic, firstNewtonQuartic, Fin.sum_univ_succ,
    nb, prod_range_succ, pt_zero, orbitCoeffs, coeffs]
  ring

/-- Actual next quartic in the same node coordinates. -/
theorem nextQuartic_newton (i : ℕ) :
    nextQuartic a b i = nextNewtonQuartic
      (fun j : Fin 4 => orbitCoeffs a b (i + 1) j.castSucc)
      (fun j : Fin 4 => pt a b i ((j : ℕ) + 1)) := by
  rw [nextQuartic, orbitQuartic_newton]
  simp [firstNewtonQuartic, nextNewtonQuartic, add_comp, mul_comp, sub_comp,
    C_comp, X_comp, pt, kk, map_sub, Nat.add_assoc]
  ring

lemma orbit_fourthNode (hba : b < a) {i : ℕ} (hi : i + 5 < P a b) :
    fourthNode (patternRho a b i) (patternU a b i) (patternV a b i)
      (pt a b i 1) (pt a b i 2) (pt a b i 3) = pt a b i 4 := by
  have h := orbitCoeffs_first_moment hba hi
  rw [orbitCoeffs_eq] at h
  simp [coeffs, Fin.sum_univ_succ, pt_zero] at h
  dsimp [fourthNode]
  linear_combination -h

lemma orbit_kernel_linear (hba : b < a) {i : ℕ} (hi : i + 5 < P a b) :
    -patternRho a b i * kk a b i + patternU a b i * kk a b (i + 1) +
      patternV a b i * kk a b (i + 2) + kk a b (i + 3) = 0 := by
  have hL := orbit_label_ne_zero hba hi
  have he : -(Lz a b (i + 1) : ℝ) * (kq a b i : ℝ) +
      (U1z a b i : ℝ) * (kq a b (i + 1) : ℝ) +
      (U2z a b i : ℝ) * (kq a b (i + 2) : ℝ) +
      (Lz a b i : ℝ) * (kq a b (i + 3) : ℝ) = 0 := by
    exact_mod_cast e0_at (a := a) (b := b) i
  simp only [patternRho, patternU, patternV, kk, kq] at he ⊢
  push_cast at he
  field_simp
  linear_combination he

/-- The five gap coordinates after the two linear eliminations are the actual gaps. -/
theorem orbit_lineGaps (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    lineGaps (patternRho a b i) (patternU a b i) (patternV a b i)
      (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
      (pt a b i 1) (pt a b i 2) (pt a b i 3) = fun j : Fin 5 => kk a b (i + j) := by
  have he := orbit_kernel_linear hba (by omega : i + 1 + 5 < P a b)
  simp only [Nat.add_assoc] at he
  unfold lineGaps
  rw [orbit_fourthNode hba (by omega)]
  funext j
  fin_cases j <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk,
    Matrix.cons_val, pt, kk, Nat.add_assoc, Nat.add_zero] at he ⊢
  all_goals first | (solve | ring) | linear_combination -he

/-- The six node coordinates after elimination are the actual quotient differences. -/
theorem orbit_lineNodes (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    lineNodes (patternRho a b i) (patternU a b i) (patternV a b i)
      (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
      (pt a b i 1) (pt a b i 2) (pt a b i 3) = fun j : Fin 6 => pt a b i j := by
  unfold lineNodes
  rw [orbit_fourthNode hba (by omega), orbit_lineGaps hba hi]
  funext j
  fin_cases j <;> simp [pt, kk, Nat.add_assoc]

lemma orbit_kernel_quadratic (hba : b < a) {i : ℕ} (hi : i + 5 < P a b) :
    -patternRho a b i * (kk a b i * (pt a b i 0 + pt a b i 1) + kk a b (i + 1)) +
      patternU a b i * (kk a b (i + 1) * (pt a b i 1 + pt a b i 2) + kk a b (i + 2)) +
      patternV a b i * (kk a b (i + 2) * (pt a b i 2 + pt a b i 3) + kk a b (i + 3)) +
      (kk a b (i + 3) * (pt a b i 3 + pt a b i 4) + kk a b (i + 4)) = 0 := by
  have h := orbitCoeffs_second_moment hba hi
  have h1 := orbitCoeffs_first_moment hba hi
  rw [orbitCoeffs_eq, coeffs_sum_mul] at h h1
  simp [pt, kk, Nat.add_assoc] at h h1 ⊢
  linear_combination h + h1

/-- The next quadratic relation expressed relative to the current origin. -/
lemma orbit_next_kernel_quadratic (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    -patternRho a b (i + 1) *
        (kk a b (i + 1) * (pt a b i 1 + pt a b i 2) + kk a b (i + 2)) +
      patternU a b (i + 1) *
        (kk a b (i + 2) * (pt a b i 2 + pt a b i 3) + kk a b (i + 3)) +
      patternV a b (i + 1) *
        (kk a b (i + 3) * (pt a b i 3 + pt a b i 4) + kk a b (i + 4)) +
      (kk a b (i + 4) * (pt a b i 4 + pt a b i 5) + kk a b (i + 5)) = 0 := by
  have h := orbit_kernel_quadratic hba (by omega : i + 1 + 5 < P a b)
  have h1 := orbit_kernel_linear hba (by omega : i + 1 + 5 < P a b)
  simp [pt, kk, Nat.add_assoc] at h h1 ⊢
  linear_combination h + 2 * ((qq a b (i + 1) : ℝ) - qq a b i) * h1

/-- The eliminated sixth gap is the actual next gap, by the next quadratic equation. -/
theorem orbit_extendedLineGaps (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    extendedLineGaps (patternRho a b i) (patternU a b i) (patternV a b i)
      (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
      (pt a b i 1) (pt a b i 2) (pt a b i 3) = fun j : Fin 6 => kk a b (i + j) := by
  have he := orbit_next_kernel_quadratic hba hi
  unfold extendedLineGaps
  rw [orbit_lineGaps hba hi, orbit_lineNodes hba hi]
  funext j
  fin_cases j <;> simp
  linear_combination -he

/-- The actual state lies on the first quadratic after all eliminations. -/
theorem orbit_lineQuadratic_zero (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    lineQuadratic (patternRho a b i) (patternU a b i) (patternV a b i)
      (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
      (pt a b i 1) (pt a b i 2) (pt a b i 3) = 0 := by
  unfold lineQuadratic
  rw [orbit_lineNodes hba hi, orbit_lineGaps hba hi]
  exact orbitCoeffs_second_moment hba (by omega)

/-- The eliminated cubic at the state is exactly its strictly positive norm. -/
theorem orbit_lineNorm_eq (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    lineNorm (patternRho a b i) (patternU a b i) (patternV a b i)
      (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
      (pt a b i 1) (pt a b i 2) (pt a b i 3) = orbitNorm a b i := by
  unfold lineNorm
  rw [orbit_lineNodes hba hi, orbit_extendedLineGaps hba hi]
  rfl

end PierceLengthBound.FixedDividend
