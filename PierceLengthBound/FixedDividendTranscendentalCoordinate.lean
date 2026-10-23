/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib

/-!
# Coordinate evaluation kernels

Successively fixing three coordinates gives a strict chain of prime evaluation
kernels, so the kernel of evaluation at a point has height at least three.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Evaluate the first `n` coordinates, leaving all later coordinates free. -/
def partialCoordinateEval {K : Type*} [CommRing K] (c : Fin 3 → K) (n : ℕ) :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K :=
  eval₂Hom C (fun j => if j.val < n then C (c j) else X j)

@[simp] lemma partialCoordinateEval_C {K : Type*} [CommRing K] (c : Fin 3 → K) (n : ℕ) (a : K) :
    partialCoordinateEval c n (C a) = C a := by simp [partialCoordinateEval]

@[simp] lemma partialCoordinateEval_X {K : Type*} [CommRing K] (c : Fin 3 → K) (n : ℕ) (j : Fin 3) :
    partialCoordinateEval c n (X j) = if j.val < n then C (c j) else X j := by
  simp [partialCoordinateEval]

lemma partialCoordinateEval_comp {K : Type*} [CommRing K] (c : Fin 3 → K)
    {m n : ℕ} (hmn : m ≤ n) :
    (partialCoordinateEval c n).comp (partialCoordinateEval c m) = partialCoordinateEval c n := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro j
    by_cases hj : j.val < m
    · have hn : j.val < n := lt_of_lt_of_le hj hmn
      simp [hj, hn]
    · simp [hj]

lemma partialCoordinateEval_ker_lt {K : Type*} [Field K] (c : Fin 3 → K)
    {n : ℕ} (hn : n < 3) :
    RingHom.ker (partialCoordinateEval c n) < RingHom.ker (partialCoordinateEval c (n + 1)) := by
  have hle : RingHom.ker (partialCoordinateEval c n) ≤
      RingHom.ker (partialCoordinateEval c (n + 1)) := by
    intro f hf
    change partialCoordinateEval c n f = 0 at hf
    have hcomp := congrArg (fun φ : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K => φ f)
      (partialCoordinateEval_comp c (show n ≤ n + 1 by omega))
    change partialCoordinateEval c (n + 1) (partialCoordinateEval c n f) = _ at hcomp
    rw [hf, map_zero] at hcomp
    exact hcomp.symm
  apply lt_of_le_of_ne hle
  intro heq
  let j : Fin 3 := ⟨n, hn⟩
  have hmem : X j - C (c j) ∈ RingHom.ker (partialCoordinateEval c (n + 1)) := by
    simp [RingHom.mem_ker, j]
  rw [← heq] at hmem
  have hzero : (X j - C (c j) : MvPolynomial (Fin 3) K) = 0 := by
    simpa [RingHom.mem_ker, j] using hmem
  have hc := congrArg (fun p : MvPolynomial (Fin 3) K => p.coeff (Finsupp.single j 1)) hzero
  have hsingle : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single j 1 := by
    intro h
    have := DFunLike.congr_fun h j
    simp at this
  simp [hsingle] at hc

/-- Fixing all three coordinates gives a prime ideal of height at least three. -/
lemma three_le_height_coordinate_kernel {K : Type*} [Field K] (c : Fin 3 → K) :
    3 ≤ (RingHom.ker (partialCoordinateEval c 3)).height := by
  let inst (n : ℕ) : (RingHom.ker (partialCoordinateEval c n)).IsPrime := RingHom.ker_isPrime _
  have h0 := Ideal.height_add_one_le_of_lt_of_isPrime
    (partialCoordinateEval_ker_lt c (n := 0) (by omega))
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime
    (partialCoordinateEval_ker_lt c (n := 1) (by omega))
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime
    (partialCoordinateEval_ker_lt c (n := 2) (by omega))
  have h01 : (1 : ℕ∞) ≤ (RingHom.ker (partialCoordinateEval c 1)).height := by
    calc
      1 = (0 : ℕ∞) + 1 := by norm_num
      _ ≤ (RingHom.ker (partialCoordinateEval c 0)).height + 1 := by gcongr; exact bot_le
      _ ≤ _ := h0
  have h12 : (2 : ℕ∞) ≤ (RingHom.ker (partialCoordinateEval c 2)).height := by
    calc
      2 = (1 : ℕ∞) + 1 := by norm_num
      _ ≤ (RingHom.ker (partialCoordinateEval c 1)).height + 1 := by gcongr
      _ ≤ _ := h1
  calc
    3 = (2 : ℕ∞) + 1 := by norm_num
    _ ≤ (RingHom.ker (partialCoordinateEval c 2)).height + 1 := by gcongr
    _ ≤ _ := h2

end
end PierceLengthBound.FixedDividend
