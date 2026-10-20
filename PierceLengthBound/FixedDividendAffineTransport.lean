/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalComponents

/-! Affine coordinate changes preserve the exact filtered Hilbert function. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Substitution by affine linear polynomials never increases total degree. -/
theorem affine_hom_totalDegree_le {K σ τ : Type*} [Field K]
    (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (hφ : ∀ j, (φ (X j)).totalDegree ≤ 1) (f : MvPolynomial σ K) :
    (φ f).totalDegree ≤ f.totalDegree := by
  classical
  have hm (m : σ →₀ ℕ) (c : K) : (φ (monomial m c)).totalDegree ≤ m.sum (fun _ n => n) := by
    rw [monomial_eq, map_mul]
    have hc : φ (C c) = C c := φ.commutes c
    rw [hc]
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    rw [Finsupp.prod, map_prod]
    apply (totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [map_pow]
    exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m j) (hφ j))
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro m hmemb
  exact (hm m (f.coeff m)).trans (le_totalDegree hmemb)

/-- An affine algebra equivalence preserves total degree exactly when its inverse
also takes coordinates to affine linear polynomials. -/
theorem affine_equiv_totalDegree {K σ τ : Type*} [Field K]
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K)
    (he : ∀ j, (e (X j)).totalDegree ≤ 1)
    (hi : ∀ j, (e.symm (X j)).totalDegree ≤ 1) (f : MvPolynomial σ K) :
    (e f).totalDegree = f.totalDegree := by
  apply le_antisymm (affine_hom_totalDegree_le e.toAlgHom he f)
  simpa using affine_hom_totalDegree_le e.symm.toAlgHom hi (e f)

/-- The induced quotient equivalence maps every filtered coordinate space exactly. -/
theorem affine_equiv_filteredCoordinateSpace {K σ τ : Type*} [Field K]
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K)
    (he : ∀ j, (e (X j)).totalDegree ≤ 1)
    (hi : ∀ j, (e.symm (X j)).totalDegree ≤ 1)
    (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    (filteredCoordinateSpace I N).map
      (Ideal.quotientEquivAlg I (I.map e.toRingHom) e rfl).toLinearEquiv.toLinearMap =
      filteredCoordinateSpace (I.map e.toRingHom) N := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hy
    apply Submodule.mem_map.mpr
    refine ⟨e f, ?_, rfl⟩
    rw [mem_restrictTotalDegree] at hf ⊢
    rwa [affine_equiv_totalDegree e he hi]
  · intro hx
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
    apply Submodule.mem_map.mpr
    refine ⟨(Ideal.Quotient.mk I) (e.symm f), ?_, ?_⟩
    · apply Submodule.mem_map.mpr
      refine ⟨e.symm f, ?_, rfl⟩
      rw [mem_restrictTotalDegree] at hf ⊢
      rwa [affine_equiv_totalDegree e.symm hi he]
    · change (Ideal.Quotient.mk (I.map e.toRingHom)) (e (e.symm f)) = _
      rw [e.apply_symm_apply]
      rfl

/-- Exact Hilbert-function invariance under an invertible affine change. -/
theorem affine_equiv_filtered_finrank {K σ τ : Type*} [Field K]
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K)
    (he : ∀ j, (e (X j)).totalDegree ≤ 1)
    (hi : ∀ j, (e.symm (X j)).totalDegree ≤ 1)
    (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace (I.map e.toRingHom) N) =
      Module.finrank K (filteredCoordinateSpace I N) := by
  rw [← affine_equiv_filteredCoordinateSpace e he hi I N]
  exact (Submodule.equivMapOfInjective
    (Ideal.quotientEquivAlg I (I.map e.toRingHom) e rfl).toLinearEquiv.toLinearMap
    (Ideal.quotientEquivAlg I (I.map e.toRingHom) e rfl).injective
    (filteredCoordinateSpace I N)).finrank_eq.symm

/-- In particular, the actual eventual Hilbert slope is preserved. -/
theorem affine_equiv_degree {K σ τ : Type*} [Field K]
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K)
    (he : ∀ j, (e (X j)).totalDegree ≤ 1)
    (hi : ∀ j, (e.symm (X j)).totalDegree ≤ 1)
    (I : Ideal (MvPolynomial σ K)) (d : ℕ)
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace (I.map e.toRingHom) n) : ℤ) = (d : ℤ) * n + c := by
  simpa only [affine_equiv_filtered_finrank e he hi] using hd

end
end PierceLengthBound.FixedDividend
