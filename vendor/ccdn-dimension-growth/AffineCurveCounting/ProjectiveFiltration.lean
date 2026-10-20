/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import AffineCurveCounting.CoordinatePowerGeneration
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The filtered homogeneous coordinate algebra

Adapted from the generic projective-filtration construction in pierce-length-bound.

For an affine coordinate ideal `I`, this constructs the subalgebra of
`(K[x]/I)[w]` whose coefficient of `w^n` is represented by a polynomial of degree
at most `n`. Its homogeneous pieces recover the existing filtered Hilbert
function. Multiplication by the homogenizing coordinate identifies the previous
filtered space inside the next piece.
-/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

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

lemma mem_projectiveCoordinateAlgebra {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (f : Polynomial (MvPolynomial σ K ⧸ I)) :
    f ∈ projectiveCoordinateAlgebra I ↔
      ∀ n, f.coeff n ∈ filteredCoordinateSpace I n := Iff.rfl

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

/-- The new coordinate `w` in the homogeneous coordinate algebra. -/
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

lemma projectiveCoordinatePiece_finrank {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Module.finrank K (projectiveCoordinatePiece I n) =
      Module.finrank K (filteredCoordinateSpace I n) := by
  exact (Submodule.equivMapOfInjective
    ((Polynomial.monomial (R := MvPolynomial σ K ⧸ I) n).restrictScalars K)
    (Polynomial.monomial_injective n) (filteredCoordinateSpace I n)).finrank_eq.symm

instance projectiveCoordinatePiece_finite {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Module.Finite K (projectiveCoordinatePiece I n) := by
  unfold projectiveCoordinatePiece
  infer_instance

/-- Multiples of the infinity coordinate from the previous homogeneous piece. -/
def projectiveInfinityMultiples {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Submodule K (Polynomial (MvPolynomial σ K ⧸ I)) :=
  (projectiveCoordinatePiece I n).map (LinearMap.mulLeft K Polynomial.X)

lemma projectiveInfinityMultiples_eq {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    projectiveInfinityMultiples I n =
      (filteredCoordinateSpace I n).map
        ((Polynomial.monomial (R := MvPolynomial σ K ⧸ I) (n + 1)).restrictScalars K) := by
  rw [projectiveInfinityMultiples, projectiveCoordinatePiece, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro a
  exact Polynomial.X_mul_monomial n a

lemma projectiveInfinityMultiples_le {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    projectiveInfinityMultiples I n ≤ projectiveCoordinatePiece I (n + 1) := by
  rw [projectiveInfinityMultiples_eq, projectiveCoordinatePiece]
  exact Submodule.map_mono (filteredCoordinateSpace_mono I (by omega))

lemma projectiveInfinityMultiples_finrank {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Module.finrank K (projectiveInfinityMultiples I n) =
      Module.finrank K (filteredCoordinateSpace I n) := by
  rw [projectiveInfinityMultiples_eq]
  exact (Submodule.equivMapOfInjective
    ((Polynomial.monomial (R := MvPolynomial σ K ⧸ I) (n + 1)).restrictScalars K)
    (Polynomial.monomial_injective (n + 1)) (filteredCoordinateSpace I n)).finrank_eq.symm

/-- The homogeneous piece after setting the infinity coordinate to zero. -/
abbrev projectiveInfinityPiece {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :=
  projectiveCoordinatePiece I (n + 1) ⧸
    (projectiveInfinityMultiples I n).comap (projectiveCoordinatePiece I (n + 1)).subtype

/-- The exact Hilbert-function difference furnished by the infinity section. -/
theorem projectiveInfinityPiece_finrank {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Module.finrank K (projectiveInfinityPiece I n) +
      Module.finrank K (filteredCoordinateSpace I n) =
      Module.finrank K (filteredCoordinateSpace I (n + 1)) := by
  let V := projectiveCoordinatePiece I (n + 1)
  let U := (projectiveInfinityMultiples I n).comap V.subtype
  have h := Submodule.finrank_quotient_add_finrank U
  have hU : Module.finrank K U = Module.finrank K (projectiveInfinityMultiples I n) := by
    rw [← Submodule.finrank_map_subtype_eq V U, Submodule.map_comap_subtype]
    rw [inf_eq_right.mpr (projectiveInfinityMultiples_le I n)]
  rw [hU, projectiveInfinityMultiples_finrank, projectiveCoordinatePiece_finrank] at h
  exact h

/-- A certified affine Hilbert slope is the eventual homogeneous-section dimension. -/
theorem projectiveInfinityPiece_eventually_degree {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) {d N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b) :
    ∀ n ≥ N, Module.finrank K (projectiveInfinityPiece I n) = d := by
  intro n hn
  have h0 := hdegree n hn
  have h1 := hdegree (n + 1) (by omega)
  have hs := projectiveInfinityPiece_finrank I n
  push_cast at h1
  nlinarith

end
end AffineCurveCounting
