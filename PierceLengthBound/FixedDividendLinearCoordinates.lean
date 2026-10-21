/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendAffineTransport

/-! Rational linear coordinate changes and the curve degree used in lattice counting. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Matrix

/-- Substitute the rows of a matrix as linear forms. -/
def matrixSubstitution {K ι : Type*} [Field K] [Fintype ι]
    (C : Matrix ι ι K) : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
  aeval fun i => ∑ j, MvPolynomial.C (C i j) * X j

lemma matrixSubstitution_X {K ι : Type*} [Field K] [Fintype ι]
    (C : Matrix ι ι K) (i : ι) : matrixSubstitution C (X i) =
      ∑ j, MvPolynomial.C (C i j) * X j := aeval_X _ _

@[simp] lemma matrixSubstitution_C {K ι : Type*} [Field K] [Fintype ι]
    (C : Matrix ι ι K) (c : K) : matrixSubstitution C (MvPolynomial.C c) =
      MvPolynomial.C c := aeval_C _ _

/-- Matrix multiplication agrees with composition in the contravariant order. -/
lemma matrixSubstitution_comp {K ι : Type*} [Field K] [Fintype ι]
    (C D : Matrix ι ι K) :
    (matrixSubstitution C).comp (matrixSubstitution D) = matrixSubstitution (D * C) := by
  classical
  ext i : 1
  simp only [AlgHom.comp_apply, matrixSubstitution_X, map_sum, map_mul, matrixSubstitution_C,
    Matrix.mul_apply, Finset.mul_sum, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma matrixSubstitution_one {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    matrixSubstitution (1 : Matrix ι ι K) = AlgHom.id K (MvPolynomial ι K) := by
  ext i : 1
  simp [matrixSubstitution_X, Matrix.one_apply]

/-- A matrix with an explicit two-sided inverse gives a polynomial algebra equivalence. -/
def matrixCoordinateEquiv {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (C D : Matrix ι ι K) (hCD : C * D = 1) (hDC : D * C = 1) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial ι K :=
  AlgEquiv.ofAlgHom (matrixSubstitution C) (matrixSubstitution D)
    (by rw [matrixSubstitution_comp, hDC, matrixSubstitution_one])
    (by rw [matrixSubstitution_comp, hCD, matrixSubstitution_one])

lemma matrixSubstitution_X_degree {K ι : Type*} [Field K] [Fintype ι]
    (C : Matrix ι ι K) (i : ι) : (matrixSubstitution C (X i)).totalDegree ≤ 1 := by
  rw [matrixSubstitution_X]
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C, totalDegree_X, zero_add, le_refl])

/-- Evaluation of the changed equations is evaluation at the changed point. -/
lemma eval_matrixSubstitution {K ι : Type*} [Field K] [Fintype ι]
    (C : Matrix ι ι K) (y : ι → K) (f : MvPolynomial ι K) :
    eval y (matrixSubstitution C f) = eval (C *ᵥ y) f := by
  have he : (aeval y).comp (matrixSubstitution C) = aeval (C *ᵥ y) := by
    ext i : 1
    simp [matrixSubstitution_X, Matrix.mulVec, dotProduct]
  exact congrArg (fun φ : MvPolynomial ι K →ₐ[K] K => φ f) he

/-- The invertible matrix substitution preserves every filtered dimension. -/
theorem matrix_coordinate_filtered_finrank {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (C D : Matrix ι ι K) (hCD : C * D = 1) (hDC : D * C = 1)
    (I : Ideal (MvPolynomial ι K)) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace (I.map (matrixSubstitution C).toRingHom) N) =
      Module.finrank K (filteredCoordinateSpace I N) := by
  exact affine_equiv_filtered_finrank (matrixCoordinateEquiv C D hCD hDC)
    (matrixSubstitution_X_degree C) (matrixSubstitution_X_degree D) I N

/-- Full Hilbert-degree invariance for the linear substitutions needed by lattices. -/
theorem matrix_coordinate_degree {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (C D : Matrix ι ι K) (hCD : C * D = 1) (hDC : D * C = 1)
    (I : Ideal (MvPolynomial ι K)) (d : ℕ)
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace (I.map (matrixSubstitution C).toRingHom) n) : ℤ) =
        (d : ℤ) * n + c := by
  simpa only [matrix_coordinate_filtered_finrank C D hCD hDC] using hd

/-- A nonsingular matrix preserves the exact filtered Hilbert function. -/
theorem nonsingular_matrix_filtered_finrank {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι K) (hC : C.det ≠ 0) (I : Ideal (MvPolynomial ι K)) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace (I.map (matrixSubstitution C).toRingHom) N) =
      Module.finrank K (filteredCoordinateSpace I N) :=
  matrix_coordinate_filtered_finrank C C⁻¹ (C.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hC))
    (C.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hC)) I N

/-- Prime curve ideals remain prime under a nonsingular matrix change. -/
theorem matrix_coordinate_prime {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι K) (hC : C.det ≠ 0) (I : Ideal (MvPolynomial ι K)) [I.IsPrime] :
    (I.map (matrixSubstitution C).toRingHom).IsPrime := by
  let e := matrixCoordinateEquiv C C⁻¹ (C.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hC))
    (C.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hC))
  apply Ideal.map_isPrime_of_surjective (f := e.toRingHom) e.surjective
  intro f hf
  have he : e f = 0 := hf
  have hz : f = 0 := e.injective (he.trans (map_zero e).symm)
  rw [hz]
  exact I.zero_mem

/-- The zero locus over `K` transforms with its equations. -/
theorem matrix_coordinate_zeroLocus {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι K) (hC : C.det ≠ 0)
    (I : Ideal (MvPolynomial ι K)) (y : ι → K) :
    y ∈ coordinateZeroLocus (I.map (matrixSubstitution C).toRingHom) ↔
      C *ᵥ y ∈ coordinateZeroLocus I := by
  let e := matrixCoordinateEquiv C C⁻¹ (C.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hC))
    (C.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hC))
  constructor
  · intro hy f hf
    have h := hy (matrixSubstitution C f) (Ideal.mem_map_of_mem _ hf)
    rwa [eval_matrixSubstitution] at h
  · intro hy f hf
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hf
    change eval y (matrixSubstitution C g) = 0
    rw [eval_matrixSubstitution]
    exact hy g hg

/-- A finite component cover remains a cover after changing coordinates, without
increasing its cardinality. -/
theorem matrix_coordinate_component_cover {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι K) (hC : C.det ≠ 0)
    (S : Finset (Ideal (MvPolynomial ι K))) :
    ∃ S' : Finset (Ideal (MvPolynomial ι K)), S'.card ≤ S.card ∧
      (∀ y, (∃ I ∈ S', y ∈ coordinateZeroLocus I) ↔
        ∃ I ∈ S, C *ᵥ y ∈ coordinateZeroLocus I) ∧
      ∀ J ∈ S', ∃ I ∈ S, J = I.map (matrixSubstitution C).toRingHom := by
  classical
  refine ⟨S.image (fun I => I.map (matrixSubstitution C).toRingHom), Finset.card_image_le, ?_, ?_⟩
  · intro y
    constructor
    · rintro ⟨J, hJ, hy⟩
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
      exact ⟨I, hI, (matrix_coordinate_zeroLocus C hC I y).mp hy⟩
    · rintro ⟨I, hI, hy⟩
      exact ⟨_, Finset.mem_image.mpr ⟨I, hI, rfl⟩,
        (matrix_coordinate_zeroLocus C hC I y).mpr hy⟩
  · intro J hJ
    obtain ⟨I, hI, he⟩ := Finset.mem_image.mp hJ
    exact ⟨I, hI, he.symm⟩

end
end PierceLengthBound.FixedDividend
