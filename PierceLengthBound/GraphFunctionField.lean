/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftGraph
public import PierceLengthBound.LinearFunctionDegree

/-! A rational graph has the same function field as its original component.
This allows the Hilbert-degree bound for linear functions to be applied to
linear combinations of the actual rational graph coordinates. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial
open scoped IntermediateField

def graphFieldMap {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (D : MvPolynomial σ K)
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hD : ι (Ideal.Quotient.mk I D) ≠ 0) :
    graphLocalization I D →ₐ[K] F :=
  IsLocalization.Away.liftAlgHom (Ideal.Quotient.mk I D) (f := ι)
    (isUnit_iff_ne_zero.mpr hD)

@[simp] theorem graphFieldMap_algebraMap {K σ F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (D : MvPolynomial σ K)
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hD : ι (Ideal.Quotient.mk I D) ≠ 0)
    (x : MvPolynomial σ K ⧸ I) :
    graphFieldMap I D ι hD (algebraMap _ (graphLocalization I D) x) = ι x := by
  simp [graphFieldMap, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem graphFieldMap_invSelf {K σ F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (D : MvPolynomial σ K)
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hD : ι (Ideal.Quotient.mk I D) ≠ 0) :
    graphFieldMap I D ι hD (IsLocalization.Away.invSelf (Ideal.Quotient.mk I D)) =
      (ι (Ideal.Quotient.mk I D))⁻¹ := by
  have h := congrArg (graphFieldMap I D ι hD)
    (IsLocalization.Away.mul_invSelf (S := graphLocalization I D) (Ideal.Quotient.mk I D))
  rw [map_mul, map_one, graphFieldMap_algebraMap] at h
  exact eq_inv_of_mul_eq_one_right h

theorem graphFieldMap_injective {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (D : MvPolynomial σ K)
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hι : Function.Injective ι)
    (hD : ι (Ideal.Quotient.mk I D) ≠ 0) : Function.Injective (graphFieldMap I D ι hD) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (Ideal.Quotient.mk I D)) (graphFieldMap I D ι hD).toRingHom).mpr
  intro x y
  constructor
  · exact congrArg (graphFieldMap I D ι hD)
  · intro h
    change graphFieldMap I D ι hD _ = graphFieldMap I D ι hD _ at h
    rw [graphFieldMap_algebraMap, graphFieldMap_algebraMap] at h
    exact congrArg (algebraMap _ (graphLocalization I D)) (hι h)

def jointGraphFieldQuotientMap {K σ τ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (P : τ → MvPolynomial σ K) (D : MvPolynomial σ K)
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hD : ι (Ideal.Quotient.mk I D) ≠ 0) :
    (MvPolynomial (σ ⊕ τ) K ⧸ jointGraphIdeal I P D) →ₐ[K] F :=
  Ideal.Quotient.liftₐ _ ((graphFieldMap I D ι hD).comp (jointGraphMap I P D))
    (by intro f hf; change graphFieldMap I D ι hD (jointGraphMap I P D f) = 0
        rw [show jointGraphMap I P D f = 0 from hf, map_zero])

@[simp] theorem jointGraphFieldQuotientMap_mk {K σ τ F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (P : τ → MvPolynomial σ K) (D : MvPolynomial σ K)
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hD : ι (Ideal.Quotient.mk I D) ≠ 0)
    (f : MvPolynomial (σ ⊕ τ) K) :
    jointGraphFieldQuotientMap I P D ι hD (Ideal.Quotient.mk _ f) =
      graphFieldMap I D ι hD (jointGraphMap I P D f) := rfl

theorem jointGraphFieldQuotientMap_injective {K σ τ F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (P : τ → MvPolynomial σ K) (D : MvPolynomial σ K)
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hι : Function.Injective ι)
    (hD : ι (Ideal.Quotient.mk I D) ≠ 0) :
    Function.Injective (jointGraphFieldQuotientMap I P D ι hD) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [jointGraphFieldQuotientMap_mk] at hz
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (graphFieldMap_injective I D ι hι hD) (hz.trans (map_zero _).symm)

theorem jointGraphFieldQuotientMap_isFractionRing {K σ τ F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (P : τ → MvPolynomial σ K) (D : MvPolynomial σ K)
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hι : Function.Injective ι)
    (hD : ι (Ideal.Quotient.mk I D) ≠ 0)
    (hfrac : ∀ z : F, ∃ x y : MvPolynomial σ K ⧸ I, z = ι x / ι y) :
    let G := MvPolynomial (σ ⊕ τ) K ⧸ jointGraphIdeal I P D
    let : Algebra G F := (jointGraphFieldQuotientMap I P D ι hD).toRingHom.toAlgebra
    IsFractionRing G F := by
  let G := MvPolynomial (σ ⊕ τ) K ⧸ jointGraphIdeal I P D
  let φ := jointGraphFieldQuotientMap I P D ι hD
  let : Algebra G F := φ.toRingHom.toAlgebra
  let : FaithfulSMul G F := (faithfulSMul_iff_algebraMap_injective G F).mpr
    (jointGraphFieldQuotientMap_injective I P D ι hι hD)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨x, y, hz⟩ := hfrac z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨Ideal.Quotient.mk _ (rename Sum.inl f), Ideal.Quotient.mk _ (rename Sum.inl g), ?_⟩
  change z = φ (Ideal.Quotient.mk _ (rename Sum.inl f)) /
    φ (Ideal.Quotient.mk _ (rename Sum.inl g))
  simpa only [φ, jointGraphFieldQuotientMap_mk, jointGraphMap_rename,
    graphFieldMap_algebraMap] using hz

def jointGraphFieldCoordinates {K σ τ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (P : τ → MvPolynomial σ K) (D : MvPolynomial σ K)
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) : σ ⊕ τ → F :=
  Sum.elim (fun j => ι (Ideal.Quotient.mk I (X j)))
    (fun j => ι (Ideal.Quotient.mk I (P j)) / ι (Ideal.Quotient.mk I D))

theorem jointGraphFieldQuotientMap_X {K σ τ F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (P : τ → MvPolynomial σ K) (D : MvPolynomial σ K)
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hD : ι (Ideal.Quotient.mk I D) ≠ 0)
    (j : σ ⊕ τ) :
    jointGraphFieldQuotientMap I P D ι hD (Ideal.Quotient.mk _ (X j)) =
      jointGraphFieldCoordinates I P D ι j := by
  cases j <;> simp [jointGraphFieldQuotientMap_mk, jointGraphMap,
    jointGraphFieldCoordinates, div_eq_mul_inv]

/-- Every transcendental linear combination of the actual graph coordinates
has function-field degree at most the graph's affine Hilbert degree. -/
theorem jointGraph_linear_function_degree_le {K σ τ F : Type*}
    [Field K] [Field F] [Algebra K F] [Fintype σ] [Fintype τ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (P : τ → MvPolynomial σ K) (D : MvPolynomial σ K)
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hι : Function.Injective ι)
    (hD : ι (Ideal.Quotient.mk I D) ≠ 0)
    (hfrac : ∀ z : F, ∃ x y : MvPolynomial σ K ⧸ I, z = ι x / ι y)
    {d : ℕ} (hdegree : ∃ N : ℕ, ∃ b : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace (jointGraphIdeal I P D) n) : ℤ) =
        (d : ℤ) * n + b)
    (c : σ ⊕ τ → K)
    (hx : Transcendental K (∑ j, algebraMap K F (c j) * jointGraphFieldCoordinates I P D ι j)) :
    let x := ∑ j, algebraMap K F (c j) * jointGraphFieldCoordinates I P D ι j
    Module.Finite K⟮x⟯ F ∧ Module.finrank K⟮x⟯ F ≤ d := by
  classical
  let J := jointGraphIdeal I P D
  let G := MvPolynomial (σ ⊕ τ) K ⧸ J
  let φ := jointGraphFieldQuotientMap I P D ι hD
  let : Algebra G F := φ.toRingHom.toAlgebra
  let : IsScalarTower K G F := IsScalarTower.of_algebraMap_eq (fun z => (φ.commutes z).symm)
  let : IsFractionRing G F := jointGraphFieldQuotientMap_isFractionRing I P D ι hι hD hfrac
  have hDI : D ∉ I := by
    intro h
    apply hD
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]
  let : J.IsPrime := jointGraphIdeal_isPrime I P D hDI
  let l : MvPolynomial (σ ⊕ τ) K := ∑ j, MvPolynomial.C (c j) * X j
  have hl : l.totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by simp)
  apply linear_function_degree_le_hilbert J hdegree l hl _ hx
  change φ (Ideal.Quotient.mk J l) = _
  simp only [l, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [jointGraphFieldQuotientMap_X]
  congr 1
  exact φ.commutes (c j)

end
end PierceLengthBound.FixedDividend
