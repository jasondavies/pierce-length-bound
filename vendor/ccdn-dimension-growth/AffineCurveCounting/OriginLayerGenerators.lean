module

public import AffineCurveCounting.SingularTangent

/-! Homogeneous generators lifted from the actual origin-adic layers of a
plane equation, with the number at every weight bounded by its multiplicity. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Module

/-- A basis of the actual graded layer lifts to homogeneous polynomials and
reduces every element of the ideal power modulo the equation and the next power. -/
theorem exists_originLayer_generators {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (k : ℕ) :
    ∃ (r : ℕ) (g : Fin r → MvPolynomial (Fin (n + 1)) K),
      r = Module.finrank K (originLayer f k) ∧
      (∀ j, (g j).IsHomogeneous k) ∧
      ∀ u ∈ idealOfVars (Fin (n + 1)) K ^ k, ∃ c : Fin r → K,
        u - ∑ j, c j • g j ∈ originTruncationIdeal f k := by
  classical
  let b := Module.finBasis K (originLayer f k)
  let φ := (Ideal.Quotient.mkₐ K (originTruncationIdeal f k)).toLinearMap
  have hlift : ∀ j, ∃ g : MvPolynomial (Fin (n + 1)) K,
      g.IsHomogeneous k ∧ φ g = (b j).val := by
    intro j
    have hmem := (b j).property
    have hmem' : (b j).val ∈ homogeneousCoordinateSpace (originTruncationIdeal f k) k :=
      (originLayer_eq_homogeneousCoordinateSpace f k).le hmem
    exact Submodule.mem_map.mp hmem'
  choose g hg he using hlift
  refine ⟨Module.finrank K (originLayer f k), g, rfl, hg, ?_⟩
  intro u hu
  let ubar : originLayer f k := ⟨φ u, Submodule.mem_map.mpr ⟨u, hu, rfl⟩⟩
  refine ⟨fun j => b.repr ubar j, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change φ (u - ∑ j, b.repr ubar j • g j) = 0
  rw [map_sub, map_sum]
  simp only [map_smul, he]
  apply sub_eq_zero.mpr
  have hsum := congrArg Subtype.val (b.sum_repr ubar)
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using hsum.symm

/-- The singular multiplicity gives genuine homogeneous local generators at
all weights, with at most μ generators at each weight. -/
theorem exists_plane_origin_generators {K : Type*} [Field K] {μ : ℕ}
    (f : MvPolynomial (Fin 2) K) (hf : f ∈ idealOfVars (Fin 2) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) :
    ∃ (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial (Fin 2) K),
      (∀ k, r k ≤ μ) ∧ (∀ k j, (g k j).IsHomogeneous k) ∧
      ∀ k u, u ∈ idealOfVars (Fin 2) K ^ k → ∃ c : Fin (r k) → K,
        u - ∑ j, c j • g k j ∈ originTruncationIdeal f k := by
  classical
  choose r g hr hg hspan using fun k => exists_originLayer_generators (n := 1) f k
  refine ⟨r, g, ?_, hg, hspan⟩
  intro k
  rw [hr]
  exact plane_originLayer_finrank_le_multiplicity f hf hμ

end
end AffineCurveCounting
