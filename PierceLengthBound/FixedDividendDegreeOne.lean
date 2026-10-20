/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendCriticalGrowth

/-!
# Degree-one prime curves are affine lines

The eventual Hilbert-degree definition implies a one-dimensional increase in
successive filtered spaces. Critical growth forces every coordinate to be affine
in one transcendental coordinate, giving polynomial containment of an affine line.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma filteredCoordinateSpace_mono {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) {M N : ℕ} (h : M ≤ N) :
    filteredCoordinateSpace I M ≤ filteredCoordinateSpace I N := by
  apply Submodule.map_mono
  intro f hf
  rw [mem_restrictTotalDegree] at hf ⊢
  exact hf.trans h

lemma coordinate_mul_filtered_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (j : σ) (N : ℕ)
    {u : MvPolynomial σ K ⧸ I} (hu : u ∈ filteredCoordinateSpace I N) :
    (Ideal.Quotient.mk I) (X j) * u ∈ filteredCoordinateSpace I (N + 1) := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hu
  apply Submodule.mem_map.mpr
  refine ⟨X j * f, ?_, by simp⟩
  rw [mem_restrictTotalDegree] at hf ⊢
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_X]
  omega

/-- A prime curve of Hilbert degree one has all coordinates affine in one
transcendental coordinate. -/
theorem degree_one_coordinates_affine {K : Type*} [Field K] [IsAlgClosed K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2)
    (hdegree : ∃ N : ℕ, ∃ b : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace p n) : ℤ) = n + b) :
    ∃ (j : Fin 3) (c d : Fin 3 → K), c j ≠ 0 ∧
      Transcendental K ((Ideal.Quotient.mk p) (X j)) ∧ ∀ k,
      (Ideal.Quotient.mk p) (X k) =
        c k • (Ideal.Quotient.mk p) (X j) + algebraMap K (MvPolynomial (Fin 3) K ⧸ p) (d k) := by
  obtain ⟨N, b, hN⟩ := hdegree
  obtain ⟨j, hj⟩ := height_two_has_transcendental_coordinate p hp
  have hdim : Module.finrank K (filteredCoordinateSpace p (N + 1)) =
      Module.finrank K (filteredCoordinateSpace p N) + 1 := by
    have h0 := hN N le_rfl
    have h1 := hN (N + 1) (by omega)
    omega
  have hUone : (1 : MvPolynomial (Fin 3) K ⧸ p) ∈ filteredCoordinateSpace p N := by
    apply Submodule.mem_map.mpr
    refine ⟨1, ?_, by simp⟩
    rw [mem_restrictTotalDegree, totalDegree_one]
    omega
  have hex (k : Fin 3) : ∃ c d : K,
      (Ideal.Quotient.mk p) (X k) = c • (Ideal.Quotient.mk p) (X j) +
        algebraMap K (MvPolynomial (Fin 3) K ⧸ p) d :=
    affine_of_critical_growth (filteredCoordinateSpace p N) (filteredCoordinateSpace p (N + 1))
      (filteredCoordinateSpace_mono p (by omega)) hUone hdim hj
      (fun _ hu => coordinate_mul_filtered_mem p j N hu)
      (fun _ hu => coordinate_mul_filtered_mem p k N hu)
  choose c d hcd using hex
  have hcj : c j ≠ 0 := by
    intro hc
    have he := hcd j
    rw [hc, zero_smul, zero_add] at he
    apply hj
    rw [he]
    exact isAlgebraic_algebraMap (d j)
  exact ⟨j, c, d, hcj, hj, hcd⟩

/-- Affine coordinate formulas in a prime quotient give polynomial containment
of an affine line through each base-field-valued point. -/
theorem line_through_point_of_affine_coordinates {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime]
    (j : Fin 3) (c d : Fin 3 → K) (hcj : c j ≠ 0)
    (hj : Transcendental K ((Ideal.Quotient.mk p) (X j)))
    (hcd : ∀ k, (Ideal.Quotient.mk p) (X k) =
      c k • (Ideal.Quotient.mk p) (X j) + algebraMap K (MvPolynomial (Fin 3) K ⧸ p) (d k))
    (z : Fin 3 → K) (hz : z ∈ coordinateZeroLocus p) :
    ∃ c : Fin 3 → K, (∃ j, c j ≠ 0) ∧ ∀ f ∈ p,
      MvPolynomial.aeval
        (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X) f = 0 := by
  let x := (Ideal.Quotient.mk p) (X j)
  let φ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
    MvPolynomial.aeval (fun k => Polynomial.C (d k) + Polynomial.C (c k) * Polynomial.X)
  have hcomp : (Polynomial.aeval x).comp φ = Ideal.Quotient.mkₐ K p := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, φ, aeval_X, map_add, map_mul,
      Polynomial.aeval_C, Polynomial.aeval_X]
    rw [Ideal.Quotient.mkₐ_eq_mk, hcd k]
    have hsmul : c k • (Ideal.Quotient.mk p) (X j) =
        algebraMap K _ (c k) * (Ideal.Quotient.mk p) (X j) :=
        Algebra.smul_def (R := K) (A := MvPolynomial (Fin 3) K ⧸ p) (c k)
          ((Ideal.Quotient.mk p) (X j))
    rw [hsmul]
    exact add_comm _ _
  have hφ (f : MvPolynomial (Fin 3) K) (hf : f ∈ p) : φ f = 0 := by
    apply (transcendental_iff_injective.mp hj)
    change ((Polynomial.aeval x).comp φ) f = _
    rw [hcomp]
    simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have hpoint (k : Fin 3) : z k = d k + c k * z j := by
    have hrel : X k - (C (d k) + C (c k) * X j) ∈ p := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp only [map_sub, map_add, map_mul]
      change (Ideal.Quotient.mk p) (X k) -
        (algebraMap K _ (d k) + algebraMap K _ (c k) * (Ideal.Quotient.mk p) (X j)) = 0
      rw [hcd k]
      have hsmul : c k • (Ideal.Quotient.mk p) (X j) =
          algebraMap K _ (c k) * (Ideal.Quotient.mk p) (X j) :=
        Algebra.smul_def (R := K) (A := MvPolynomial (Fin 3) K ⧸ p) (c k)
          ((Ideal.Quotient.mk p) (X j))
      rw [hsmul]
      ring
    have he := hz _ hrel
    simpa only [eval_sub, eval_add, eval_mul, eval_X, eval_C, sub_eq_zero] using he
  have htranslate :
      (Polynomial.aeval (Polynomial.C (z j) + Polynomial.X)).comp φ =
      MvPolynomial.aeval (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, φ, aeval_X, map_add, map_mul,
      Polynomial.aeval_C, Polynomial.aeval_X]
    rw [hpoint k]
    simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.algebraMap_eq]
    ring
  refine ⟨c, ⟨j, hcj⟩, ?_⟩
  intro f hf
  rw [← htranslate, AlgHom.comp_apply, hφ f hf, map_zero]

/-- Every point on a prime curve of Hilbert degree one lies on a nonconstant
affine line contained in that prime ideal's zero locus, as a polynomial identity. -/
theorem degree_one_line_through_point {K : Type*} [Field K] [IsAlgClosed K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2)
    (hdegree : ∃ N : ℕ, ∃ b : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace p n) : ℤ) = n + b)
    (z : Fin 3 → K) (hz : z ∈ coordinateZeroLocus p) :
    ∃ c : Fin 3 → K, (∃ j, c j ≠ 0) ∧ ∀ f ∈ p,
      MvPolynomial.aeval
        (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X) f = 0 := by
  obtain ⟨j, c, d, hcj, hj, hcd⟩ := degree_one_coordinates_affine p hp hdegree
  exact line_through_point_of_affine_coordinates p j c d hcj hj hcd z hz

end
end PierceLengthBound.FixedDividend
