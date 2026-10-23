/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import PierceLengthBound.FixedDividendFilteredIntersection

/-!
# The filtered homogeneous coordinate algebra

For an affine coordinate ideal `I`, this constructs the subalgebra of
`(K[x]/I)[w]` whose coefficient of `w^n` is represented by a polynomial of degree
at most `n`, together with its homogenizing coordinate and homogeneous pieces.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

lemma filteredCoordinateSpace_mul_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) {m n : ℕ} {x y : MvPolynomial σ K ⧸ I}
    (hx : x ∈ filteredCoordinateSpace I m) (hy : y ∈ filteredCoordinateSpace I n) :
    x * y ∈ filteredCoordinateSpace I (m + n) := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hy
  apply Submodule.mem_map.mpr
  refine ⟨f * g, ?_, by simp⟩
  rw [MvPolynomial.mem_restrictTotalDegree] at hf hg ⊢
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hf hg)

lemma filteredCoordinateSpace_algebraMap_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) (c : K) :
    algebraMap K (MvPolynomial σ K ⧸ I) c ∈ filteredCoordinateSpace I n := by
  apply Submodule.mem_map.mpr
  refine ⟨MvPolynomial.C c, ?_, by simp⟩
  simp [MvPolynomial.mem_restrictTotalDegree]

/-- Homogeneous coordinate algebra of the filtered affine coordinate ring. -/
def projectiveCoordinateAlgebra {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) : Subalgebra K (Polynomial (MvPolynomial σ K ⧸ I)) where
  carrier := {f | ∀ n, f.coeff n ∈ filteredCoordinateSpace I n}
  mul_mem' hf hg n := by
    rw [Polynomial.coeff_mul]
    apply Submodule.sum_mem
    rintro ⟨i, j⟩ hij
    have := filteredCoordinateSpace_mul_mem I (hf i) (hg j)
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hij] at this
  one_mem' n := by
    by_cases hn : n = 0
    · subst n
      simpa using filteredCoordinateSpace_algebraMap_mem I 0 1
    · simp [Polynomial.coeff_one, hn]
  add_mem' hf hg n := by
    rw [Polynomial.coeff_add]
    exact (filteredCoordinateSpace I n).add_mem (hf n) (hg n)
  zero_mem' n := by simp
  algebraMap_mem' c n := by
    by_cases hn : n = 0
    · subst n
      simpa using filteredCoordinateSpace_algebraMap_mem I 0 c
    · simp [Polynomial.algebraMap_apply, Polynomial.coeff_C, hn]

lemma projective_monomial_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) (a : MvPolynomial σ K ⧸ I) :
    Polynomial.monomial n a ∈ projectiveCoordinateAlgebra I ↔
      a ∈ filteredCoordinateSpace I n := by
  constructor
  · intro h
    simpa using h n
  · intro ha i
    by_cases hi : n = i
    · subst i
      simpa using ha
    · simp [Polynomial.coeff_monomial, hi]

/-- The homogenizing coordinate `w` in the homogeneous coordinate algebra. -/
def projectiveInfinityCoordinate {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) : projectiveCoordinateAlgebra I :=
  ⟨Polynomial.X, by
    rw [← Polynomial.monomial_one_one_eq_X, projective_monomial_mem]
    simpa using filteredCoordinateSpace_algebraMap_mem I 1 1⟩

/-- The degree-`n` homogeneous piece, in the ambient polynomial module. -/
def projectiveCoordinatePiece {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Submodule K (Polynomial (MvPolynomial σ K ⧸ I)) :=
  (filteredCoordinateSpace I n).map
    ((Polynomial.monomial (R := MvPolynomial σ K ⧸ I) n).restrictScalars K)

end
end PierceLengthBound.FixedDividend
