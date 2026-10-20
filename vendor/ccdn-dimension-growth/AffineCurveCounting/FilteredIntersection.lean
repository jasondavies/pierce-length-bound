/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import AffineCurveCounting.Curve
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Filtered multiples in a two-equation ideal

Adapted from the generic filtered-space lemmas in pierce-length-bound. The
intersection of the bounded-degree multiples of two coprime equations consists
exactly of bounded-degree multiples of their product.
-/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Multiples of `f` whose multiplier has the degree allowed by cutoff `N`. -/
def filteredMultiples {K σ : Type*} [Field K] (f : MvPolynomial σ K) (N : ℕ) :
    Submodule K (MvPolynomial σ K) :=
  (restrictTotalDegree σ K (N - f.totalDegree)).map (LinearMap.mulLeft K f)

lemma mem_filteredMultiples {K σ : Type*} [Field K] (f x : MvPolynomial σ K) (N : ℕ) :
    x ∈ filteredMultiples f N ↔ ∃ u, u.totalDegree ≤ N - f.totalDegree ∧ f * u = x := by
  simp [filteredMultiples, Submodule.mem_map, mem_restrictTotalDegree, LinearMap.mulLeft_apply]

lemma filteredMultiples_le_degree {K σ : Type*} [Field K] (f : MvPolynomial σ K)
    {N : ℕ} (hN : f.totalDegree ≤ N) : filteredMultiples f N ≤ restrictTotalDegree σ K N := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := (mem_filteredMultiples f x N).mp hx
  rw [mem_restrictTotalDegree]
  exact (totalDegree_mul _ _).trans (by omega)

instance filteredMultiples_finite {K σ : Type*} [Field K] [Finite σ]
    (f : MvPolynomial σ K) (N : ℕ) : Module.Finite K (filteredMultiples f N) := by
  unfold filteredMultiples
  infer_instance

lemma filteredMultiples_finrank {K σ : Type*} [Field K] (f : MvPolynomial σ K)
    (hf : f ≠ 0) (N : ℕ) :
    Module.finrank K (filteredMultiples f N) =
      Module.finrank K (restrictTotalDegree σ K (N - f.totalDegree)) := by
  exact (Submodule.equivMapOfInjective (LinearMap.mulLeft K f)
    (fun x y h => mul_left_cancel₀ hf h) _).finrank_eq.symm

/-- Exact intersection of the two spaces of bounded-degree multiples. -/
theorem filteredMultiples_inf {K σ : Type*} [Field K]
    {f g : MvPolynomial σ K} (hf : Prime f) (hfg : ¬ f ∣ g)
    {N : ℕ} (hN : f.totalDegree + g.totalDegree ≤ N) :
    filteredMultiples f N ⊓ filteredMultiples g N = filteredMultiples (f * g) N := by
  have hg : g ≠ 0 := by intro h; exact hfg (h ▸ dvd_zero f)
  have hprod := totalDegree_mul_of_isDomain hf.ne_zero hg
  ext x
  constructor
  · rintro ⟨hxf, hxg⟩
    obtain ⟨u, hu, hux⟩ := (mem_filteredMultiples f x N).mp hxf
    obtain ⟨v, hv, hvx⟩ := (mem_filteredMultiples g x N).mp hxg
    have hdvd : f ∣ g * v := ⟨u, hux.trans hvx.symm |>.symm⟩
    obtain ⟨w, hw⟩ := (hf.dvd_or_dvd hdvd).resolve_left hfg
    have hfu : f * u = f * (g * w) := by rw [hux, ← hvx, hw]; ring
    have huw : u = g * w := mul_left_cancel₀ hf.ne_zero hfu
    apply (mem_filteredMultiples (f * g) x N).mpr
    refine ⟨w, ?_, ?_⟩
    · rw [hprod]
      by_cases hw0 : w = 0
      · simp [hw0]
      rw [hw, totalDegree_mul_of_isDomain hf.ne_zero hw0] at hv
      omega
    · rw [mul_assoc, ← huw, hux]
  · intro hx
    obtain ⟨w, hw, hwx⟩ := (mem_filteredMultiples (f * g) x N).mp hx
    rw [hprod] at hw
    constructor
    · apply (mem_filteredMultiples f x N).mpr
      refine ⟨g * w, (totalDegree_mul _ _).trans (by omega), ?_⟩
      simpa [mul_assoc] using hwx
    · apply (mem_filteredMultiples g x N).mpr
      refine ⟨f * w, (totalDegree_mul _ _).trans (by omega), ?_⟩
      simpa [mul_assoc, mul_comm, mul_left_comm] using hwx


/-- Dimension inclusion-exclusion for the bounded-degree multiples. -/
theorem filteredMultiples_sup_finrank {K σ : Type*} [Field K] [Finite σ]
    {f g : MvPolynomial σ K} (hf : Prime f) (hfg : ¬ f ∣ g)
    {N : ℕ} (hN : f.totalDegree + g.totalDegree ≤ N) :
    Module.finrank K ↥(filteredMultiples f N ⊔ filteredMultiples g N) +
      Module.finrank K (restrictTotalDegree σ K (N - (f.totalDegree + g.totalDegree))) =
      Module.finrank K (restrictTotalDegree σ K (N - f.totalDegree)) +
      Module.finrank K (restrictTotalDegree σ K (N - g.totalDegree)) := by
  have hg : g ≠ 0 := by intro h; exact hfg (h ▸ dvd_zero f)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (filteredMultiples f N) (filteredMultiples g N)
  rw [filteredMultiples_inf hf hfg hN, filteredMultiples_finrank _ hf.ne_zero,
    filteredMultiples_finrank _ hg, filteredMultiples_finrank _ (mul_ne_zero hf.ne_zero hg),
    totalDegree_mul_of_isDomain hf.ne_zero hg] at h
  exact h

/-- A subspace known to lie in a linear map's kernel subtracts from the image dimension. -/
lemma finrank_map_add_kernel_subspace_le {K M W : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup W] [Module K W]
    (φ : M →ₗ[K] W) (V U : Submodule K M) [Module.Finite K V]
    (hUV : U ≤ V) (hUker : U ≤ φ.ker) :
    Module.finrank K (V.map φ) + Module.finrank K U ≤ Module.finrank K V := by
  have h := LinearMap.finrank_range_add_finrank_ker (φ.domRestrict V)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have hk := Submodule.finrank_map_subtype_eq V (φ.ker.comap V.subtype)
  rw [Submodule.map_comap_subtype] at hk
  rw [← hk] at h
  have hle := Submodule.finrank_mono (le_inf hUV hUker)
  omega

/-- Bounded-degree polynomials in the quotient coordinate ring. This agrees with
`AffineCurveCounting.coordinateSpace` when the coefficient field is `ℚ`. -/
def filteredCoordinateSpace {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (N : ℕ) : Submodule K (MvPolynomial σ K ⧸ I) :=
  (restrictTotalDegree σ K N).map (Ideal.Quotient.mkₐ K I).toLinearMap

instance filteredCoordinateSpace_finite {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (N : ℕ) : Module.Finite K (filteredCoordinateSpace I N) := by
  unfold filteredCoordinateSpace
  infer_instance

/-- The filtered Koszul rank bound, before evaluating the monomial-space dimensions.
It applies to every ideal containing the two equations. -/
theorem filteredCoordinateSpace_finrank_bound {K σ : Type*} [Field K] [Finite σ]
    {f g : MvPolynomial σ K} (hf : Prime f) (hfg : ¬ f ∣ g)
    (I : Ideal (MvPolynomial σ K)) (hIf : f ∈ I) (hIg : g ∈ I)
    {N : ℕ} (hN : f.totalDegree + g.totalDegree ≤ N) :
    Module.finrank K (filteredCoordinateSpace I N) +
      Module.finrank K (restrictTotalDegree σ K (N - f.totalDegree)) +
      Module.finrank K (restrictTotalDegree σ K (N - g.totalDegree)) ≤
      Module.finrank K (restrictTotalDegree σ K N) +
      Module.finrank K (restrictTotalDegree σ K (N - (f.totalDegree + g.totalDegree))) := by
  let φ := (Ideal.Quotient.mkₐ K I).toLinearMap
  have hker (p : MvPolynomial σ K) (hp : p ∈ I) : filteredMultiples p N ≤ φ.ker := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := (mem_filteredMultiples p x N).mp hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact I.mul_mem_right u hp
  have hbound := finrank_map_add_kernel_subspace_le φ (restrictTotalDegree σ K N)
    (filteredMultiples f N ⊔ filteredMultiples g N)
    (sup_le (filteredMultiples_le_degree f (by omega))
      (filteredMultiples_le_degree g (by omega)))
    (sup_le (hker f hIf) (hker g hIg))
  have heq := filteredMultiples_sup_finrank hf hfg hN
  change Module.finrank K (filteredCoordinateSpace I N) + _ ≤ _ at hbound
  omega

end
end AffineCurveCounting
