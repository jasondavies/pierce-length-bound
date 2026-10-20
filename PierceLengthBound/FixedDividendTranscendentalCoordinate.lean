/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendComponentSeparation
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# A transcendental coordinate on a codimension-two component

Successively fixing three coordinates gives a strict chain of prime evaluation
kernels. Over an algebraically closed field, a prime of height two must therefore
retain at least one transcendental coordinate.
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
    simpa using this
  simpa [hsingle] using hc

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


/-- An algebraic element of a domain over an algebraically closed field is scalar. -/
lemma algebraic_eq_scalar {K A : Type*} [Field K] [IsAlgClosed K] [CommRing A]
    [IsDomain A] [Algebra K A] {y : A} (hy : IsAlgebraic K y) :
    ∃ c : K, algebraMap K A c = y := by
  have hi := hy.isIntegral
  have hlead : (minpoly K y).leadingCoeff = 1 := minpoly.monic hi
  have hdegree : (minpoly K y).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hi)
  have he := minpoly.aeval K y
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hdegree, hlead, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at he
  exact ⟨-(minpoly K y).coeff 0, by simpa using he.symm⟩

/-- A prime of height two in three variables retains a transcendental coordinate. -/
theorem height_two_has_transcendental_coordinate {K : Type*} [Field K] [IsAlgClosed K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2) :
    ∃ j : Fin 3, Transcendental K ((Ideal.Quotient.mk p) (X j)) := by
  classical
  by_contra h
  push Not at h
  have ha (j : Fin 3) : IsAlgebraic K ((Ideal.Quotient.mk p) (X j)) := by
    simpa only [Transcendental, not_not] using h j
  choose c hc using fun j => algebraic_eq_scalar (ha j)
  have hcomp : (Ideal.Quotient.mk p).comp (partialCoordinateEval c 3) = Ideal.Quotient.mk p := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      simp only [RingHom.comp_apply, partialCoordinateEval_X, ite_eq_left j.isLt]
      exact hc j
  have hle : RingHom.ker (partialCoordinateEval c 3) ≤ p := by
    intro f hf
    change partialCoordinateEval c 3 f = 0 at hf
    have he := congrArg (fun φ : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K ⧸ p => φ f) hcomp
    change (Ideal.Quotient.mk p) (partialCoordinateEval c 3 f) = _ at he
    rw [hf, map_zero] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm
  have hd := (three_le_height_coordinate_kernel c).trans (Ideal.height_mono hle)
  rw [hp] at hd
  norm_num at hd

end
end PierceLengthBound.FixedDividend
