module

public import AffineCurveCounting.ProjectionFieldDegree
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! A primitive coordinate pair generates the function field over the constant
field. Every finite family of functions then has polynomial reconstruction
identities with one nonzero denominator. No bound on its degree is asserted. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma ratFunc_image_mem_of_X_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : RatFunc K →ₐ[K] F) (L : IntermediateField K F)
    (hX : φ RatFunc.X ∈ L) (r : RatFunc K) : φ r ∈ L := by
  have hp (p : Polynomial K) : φ (algebraMap (Polynomial K) (RatFunc K) p) ∈ L := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using L.add_mem hp hq
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow, RatFunc.algebraMap_X]
      apply L.mul_mem _ (pow_mem hX n)
      have hc : φ (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c)) =
          algebraMap K F c := by
        change φ (algebraMap K (RatFunc K) c) = _
        exact φ.commutes c
      rw [hc]
      exact L.algebraMap_mem c
  induction r using RatFunc.induction_on with
  | f p q _ => rw [map_div₀]; exact L.div_mem (hp p) (hp q)

/-- A primitive element over the rational parameter field, together with that
parameter, generates the entire field over K. -/
theorem primitive_ratFunc_pair_adjoin_top {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : RatFunc K →ₐ[K] F) (v : F)
    (hprim : let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K) {v} = ⊤) :
    IntermediateField.adjoin K (Set.range (![φ RatFunc.X, v] : Fin 2 → F)) = ⊤ := by
  let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  let a : Fin 2 → F := ![φ RatFunc.X, v]
  let L := IntermediateField.adjoin K (Set.range a)
  have hu : φ RatFunc.X ∈ L := IntermediateField.subset_adjoin K _ ⟨0, rfl⟩
  have hv : v ∈ L := IntermediateField.subset_adjoin K _ ⟨1, rfl⟩
  have hsub : (IntermediateField.adjoin (RatFunc K) {v} : Set F) ⊆ L := by
    apply (IntermediateField.adjoin_subset_adjoin_iff (RatFunc K) (F' := K)).mpr
    refine ⟨?_, ?_⟩
    · rintro _ ⟨r, rfl⟩
      exact ratFunc_image_mem_of_X_mem φ L hu r
    · intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact hv
  apply top_unique
  intro x _
  exact hsub (by rw [hprim]; trivial)

/-- A generating polynomial tuple expresses any field element as a quotient
with a genuinely nonzero evaluated denominator. -/
lemma adjoin_top_polynomial_fraction {K F σ : Type*} [Field K] [Field F] [Algebra K F]
    (a : σ → F) (ha : IntermediateField.adjoin K (Set.range a) = ⊤) (x : F) :
    ∃ r s : MvPolynomial σ K, aeval a s ≠ 0 ∧ x = aeval a r / aeval a s := by
  by_cases hx : x = 0
  · exact ⟨0, 1, by simp, by simp [hx]⟩
  obtain ⟨r, s, he⟩ := (IntermediateField.mem_adjoin_range_iff K a x).mp
    (by rw [ha]; trivial)
  refine ⟨r, s, ?_, he⟩
  intro hs
  apply hx
  rw [he, hs, div_zero]

/-- A finite family of field elements has a common polynomial denominator in
any generating tuple, with actual polynomial reconstruction identities. -/
theorem exists_common_polynomial_reconstruction {K F σ ι : Type*}
    [Field K] [Field F] [Algebra K F] [Fintype ι] [DecidableEq ι]
    (a : σ → F) (ha : IntermediateField.adjoin K (Set.range a) = ⊤)
    (x : ι → F) :
    ∃ Q : MvPolynomial σ K, ∃ P : ι → MvPolynomial σ K,
      aeval a Q ≠ 0 ∧ ∀ i, aeval a Q * x i = aeval a (P i) := by
  classical
  choose r s hs he using fun i => adjoin_top_polynomial_fraction a ha (x i)
  let Q := ∏ i, s i
  let P := fun i => r i * ∏ j ∈ Finset.univ.erase i, s j
  refine ⟨Q, P, ?_, ?_⟩
  · simpa only [Q, map_prod] using Finset.prod_ne_zero_iff.mpr (fun i _ => hs i)
  · intro i
    have hQ : Q = s i * ∏ j ∈ Finset.univ.erase i, s j :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [hQ, he, map_mul]
    dsimp only [P]
    rw [map_mul]
    field_simp [hs i]

end
end AffineCurveCounting
