module

public import AffineCurveCounting.MonomialDimension

/-! The exact affine Hilbert function of a principal plane equation. This
identifies polynomial total degree with the degree in the curve-counting target. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem principal_filtered_finrank {K σ : Type*} [Field K] [Finite σ]
    (f : MvPolynomial σ K) (hf : f ≠ 0) {N : ℕ} (hN : f.totalDegree ≤ N) :
    Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) N) +
      Module.finrank K (restrictTotalDegree σ K (N - f.totalDegree)) =
      Module.finrank K (restrictTotalDegree σ K N) := by
  let φ := (Ideal.Quotient.mkₐ K (Ideal.span {f})).toLinearMap
  let V := restrictTotalDegree σ K N
  have hk : V ⊓ φ.ker = filteredMultiples f N := by
    ext x
    constructor
    · rintro ⟨hx, hz⟩
      have hmem : x ∈ Ideal.span {f} := Ideal.Quotient.eq_zero_iff_mem.mp hz
      obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hmem
      apply (mem_filteredMultiples f (f * u) N).mpr
      refine ⟨u, ?_, rfl⟩
      by_cases hu : u = 0
      · simp [hu]
      have hdeg : (f * u).totalDegree ≤ N := (mem_restrictTotalDegree _ _ _).mp hx
      rw [totalDegree_mul_of_isDomain hf hu] at hdeg
      omega
    · intro hx
      refine ⟨filteredMultiples_le_degree f hN hx, ?_⟩
      obtain ⟨u, _, rfl⟩ := (mem_filteredMultiples f x N).mp hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right f u))
  have h := LinearMap.finrank_range_add_finrank_ker (φ.domRestrict V)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have he := Submodule.finrank_map_subtype_eq V (φ.ker.comap V.subtype)
  rw [Submodule.map_comap_subtype, hk, filteredMultiples_finrank f hf] at he
  rw [← he] at h
  exact h

theorem finrank_restrictTotalDegree_two {K : Type*} [Field K] (N : ℕ) :
    Module.finrank K (restrictTotalDegree (Fin 2) K N) = (N + 2).choose 2 := by
  rw [finrank_restrictTotalDegree]
  simp only [Fintype.card_fin]
  rw [Nat.add_comm 2 N, Nat.choose_symm_add]

lemma two_mul_choose_add_two (n : ℕ) :
    2 * (n + 2).choose 2 = (n + 2) * (n + 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 2) 2
  norm_num [Nat.descFactorial_succ] at h
  nlinarith

theorem principal_plane_hilbert_function {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) {N : ℕ} (hN : f.totalDegree ≤ N) :
    (Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) N) : ℤ) =
      (f.totalDegree : ℤ) * N + ((f.totalDegree : ℤ) - f.totalDegree.choose 2) := by
  have h := principal_filtered_finrank f hf hN
  rw [finrank_restrictTotalDegree_two, finrank_restrictTotalDegree_two] at h
  have h0 := two_mul_choose_add_two N
  have h1 := two_mul_choose_add_two (N - f.totalDegree)
  have h2 := Nat.descFactorial_eq_factorial_mul_choose f.totalDegree 2
  norm_num [Nat.descFactorial_succ] at h2
  have hsum : (Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) N) : ℤ) +
      ((N - f.totalDegree + 2).choose 2 : ℤ) = ((N + 2).choose 2 : ℤ) := by
    exact_mod_cast h
  have hc0 : (2 : ℤ) * ((N + 2).choose 2 : ℤ) = ((N : ℤ) + 2) * (N + 1) := by
    exact_mod_cast h0
  have hc1 : (2 : ℤ) * ((N - f.totalDegree + 2).choose 2 : ℤ) =
      ((N : ℤ) - f.totalDegree + 2) * ((N : ℤ) - f.totalDegree + 1) := by
    exact_mod_cast h1
  have hc2 : (2 : ℤ) * (f.totalDegree.choose 2 : ℤ) =
      (f.totalDegree : ℤ) * ((f.totalDegree : ℤ) - 1) := by
    cases hd : f.totalDegree with
    | zero => simp
    | succ d =>
      rw [hd] at h2
      simp only [Nat.add_sub_cancel] at h2
      push_cast
      have hcast : (d : ℤ) * (d + 1) = 2 * ((d + 1).choose 2 : ℤ) := by
        exact_mod_cast h2
      nlinarith
  nlinarith

/-- The degree used by the full counting target agrees with polynomial degree. -/
theorem principal_plane_hasAffineCurveDegree (f : CoordinatePolynomial 2) (hf : f ≠ 0) :
    HasAffineCurveDegree (Ideal.span {f}) f.totalDegree := by
  refine ⟨f.totalDegree, (f.totalDegree : ℤ) - f.totalDegree.choose 2, ?_⟩
  intro N hN
  exact principal_plane_hilbert_function f hf hN

end
end AffineCurveCounting
