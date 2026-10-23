/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendProjectiveFiltration

/-!
# An affine chart of the filtered projective closure

Evaluating the homogeneous coordinate algebra at the inverse of a nonzero linear
coordinate constructs a domain chart inside the affine function field. Its
finite-dimensional pieces are the original filtered coordinate spaces divided
by successive powers of that coordinate.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Evaluation at `w = 1 / l` through a field realization `ι` of the coordinate ring. -/
def projectiveChartEval {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) : Polynomial (MvPolynomial σ K ⧸ I) →ₐ[K] F :=
  Polynomial.aevalTower ι (ι l)⁻¹

/-- The affine chart ring, as a subalgebra of `F`. -/
def projectiveChart {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) : Subalgebra K F :=
  (projectiveCoordinateAlgebra I).map (projectiveChartEval I ι l)

/-- The homogeneous piece evaluated in the chart. -/
def projectiveChartPiece {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) (n : ℕ) : Submodule K F :=
  (projectiveCoordinatePiece I n).map (projectiveChartEval I ι l).toLinearMap

lemma projectiveChartEval_monomial {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l a : MvPolynomial σ K ⧸ I) (n : ℕ) :
    projectiveChartEval I ι l (Polynomial.monomial n a) = ι a * (ι l)⁻¹ ^ n := by
  change Polynomial.eval₂ ι.toRingHom (ι l)⁻¹ (Polynomial.monomial n a) = _
  exact Polynomial.eval₂_monomial _ _

lemma mem_projectiveChartPiece {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) (n : ℕ) (x : F) :
    x ∈ projectiveChartPiece I ι l n ↔
      ∃ a ∈ filteredCoordinateSpace I n, ι a * (ι l)⁻¹ ^ n = x := by
  simp only [projectiveChartPiece, projectiveCoordinatePiece, Submodule.mem_map,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  constructor
  · rintro ⟨p, ⟨a, ha, rfl⟩, hp⟩
    exact ⟨a, ha, (projectiveChartEval_monomial I ι l a n).symm.trans hp⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨Polynomial.monomial n a, ⟨a, ha, rfl⟩,
      (projectiveChartEval_monomial I ι l a n).trans hx⟩

lemma projectiveChartPiece_le {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) (n : ℕ) :
    projectiveChartPiece I ι l n ≤ (projectiveChart I ι l).toSubmodule := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (mem_projectiveChartPiece I ι l n x).mp hx
  exact Subalgebra.mem_map.mpr ⟨Polynomial.monomial n a,
    (projective_monomial_mem I n a).mpr ha, projectiveChartEval_monomial I ι l a n⟩

/-- Multiplication by the chosen linear coordinate nests the successive chart pieces. -/
lemma projectiveChartPiece_mono {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) (hl : l ∈ filteredCoordinateSpace I 1) (hl0 : ι l ≠ 0) :
    Monotone (projectiveChartPiece I ι l) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  obtain ⟨a, ha, rfl⟩ := (mem_projectiveChartPiece I ι l n x).mp hx
  apply (mem_projectiveChartPiece I ι l (n + 1) _).mpr
  refine ⟨a * l, filteredCoordinateSpace_mul_mem I ha hl, ?_⟩
  rw [map_mul, pow_succ]
  field_simp

/-- The chart is the union of the evaluated homogeneous pieces. -/
theorem projectiveChart_eq_iSup_pieces {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) :
    (projectiveChart I ι l).toSubmodule = ⨆ n, projectiveChartPiece I ι l n := by
  apply le_antisymm
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Subalgebra.mem_map.mp hx
    rw [p.as_sum_support, map_sum]
    apply Submodule.sum_mem
    intro n hn
    apply (le_iSup (projectiveChartPiece I ι l) n)
    apply (mem_projectiveChartPiece I ι l n _).mpr
    exact ⟨p.coeff n, hp n, (projectiveChartEval_monomial I ι l _ n).symm⟩
  · exact iSup_le (projectiveChartPiece_le I ι l)

/-- Every chart element has a single bounded-degree numerator. -/
theorem mem_projectiveChart_iff {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) (hl : l ∈ filteredCoordinateSpace I 1) (hl0 : ι l ≠ 0)
    (x : F) : x ∈ projectiveChart I ι l ↔
      ∃ n, ∃ a ∈ filteredCoordinateSpace I n, ι a * (ι l)⁻¹ ^ n = x := by
  change x ∈ (projectiveChart I ι l).toSubmodule ↔ _
  rw [projectiveChart_eq_iSup_pieces,
    Submodule.mem_iSup_of_directed _ (projectiveChartPiece_mono I ι l hl hl0).directed_le]
  simp only [mem_projectiveChartPiece]

end
end PierceLengthBound.FixedDividend
