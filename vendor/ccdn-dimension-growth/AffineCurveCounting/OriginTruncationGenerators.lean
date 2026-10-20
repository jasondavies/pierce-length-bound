module

public import AffineCurveCounting.OriginLayerGenerators

/-! Finite-precision generation of actual singular plane-curve local quotients.
The generators have controlled weights and at most μ generators at each weight. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Successive actual layer reductions assemble into a finite-precision
polynomial representation, modulo the defining equation and the Nth origin power. -/
lemma origin_layers_generate_truncation {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (r : ℕ → ℕ)
    (g : (k : ℕ) → Fin (r k) → MvPolynomial σ K)
    (hspan : ∀ k u, u ∈ idealOfVars σ K ^ k → ∃ c : Fin (r k) → K,
      u - ∑ j, c j • g k j ∈ originTruncationIdeal f k)
    (N : ℕ) (u : MvPolynomial σ K) :
    ∃ c : (k : Fin N) → Fin (r k.val) → K,
      u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈ Ideal.span {f} ⊔ idealOfVars σ K ^ N := by
  induction N with
  | zero =>
    refine ⟨fun k => Fin.elim0 k, ?_⟩
    simp
  | succ N ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨p, hp, q, hq, he⟩ := Submodule.mem_sup.mp hc
    obtain ⟨b, hb⟩ := hspan N q hq
    let c' : (k : Fin (N + 1)) → Fin (r k.val) → K := Fin.lastCases b c
    refine ⟨c', ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [c', Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, Fin.val_last]
    have hp' : p ∈ Ideal.span {f} ⊔ idealOfVars σ K ^ (N + 1) := Submodule.mem_sup_left hp
    have hadd := (Ideal.span {f} ⊔ idealOfVars σ K ^ (N + 1)).add_mem hp' hb
    convert hadd using 1
    linear_combination -he

/-- Genuine finite-precision weighted generators for any plane equation of
multiplicity μ. No graded-ring presentation or spanning hypothesis is assumed. -/
theorem exists_plane_truncation_generators {K : Type*} [Field K] {μ : ℕ}
    (f : MvPolynomial (Fin 2) K) (hf : f ∈ idealOfVars (Fin 2) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) :
    ∃ (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial (Fin 2) K),
      (∀ k, r k ≤ μ) ∧ (∀ k j, (g k j).IsHomogeneous k) ∧
      ∀ N u, ∃ c : (k : Fin N) → Fin (r k.val) → K,
        u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈
          Ideal.span {f} ⊔ idealOfVars (Fin 2) K ^ N := by
  obtain ⟨r, g, hr, hg, hs⟩ := exists_plane_origin_generators f hf hμ
  exact ⟨r, g, hr, hg, origin_layers_generate_truncation f r g hs⟩

end
end AffineCurveCounting
