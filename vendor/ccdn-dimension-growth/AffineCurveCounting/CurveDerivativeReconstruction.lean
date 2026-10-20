module

public import AffineCurveCounting.PlaneDeformationRelation

/-! A degree-preserving linear plane projection admits reconstruction using
the partial derivative of its image equation. This bounds the common
denominator's degree by d-1 without normalization or a genus formula. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Differentiate an actual family of degree-d plane equations to reconstruct
any linear source function using the same derivative denominator. -/
theorem exists_derivative_reconstruction {K τ : Type*}
    [Field K] [CharZero K] [Fintype τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin 2 → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c)
    (hu : Transcendental K ((Ideal.Quotient.mk I) (a 0)))
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hfd : f.totalDegree = d)
    (hker : ∀ g, aeval a g ∈ I ↔ f ∣ g)
    (l : MvPolynomial τ K) (hl : l.totalDegree ≤ 1) :
    ∃ P : MvPolynomial (Fin 2) K, P.totalDegree ≤ d ∧
      aeval a (pderiv 1 f) * l - aeval a P ∈ I := by
  classical
  let V := restrictTotalDegree (Fin 2) K d
  let b := Module.finBasis K V
  obtain ⟨v, hv, j, hj⟩ := exists_curve_projection_relation_family I a ha d hdegree hu l hl
  let r := fun i => (b i).val
  let f₀ := ∑ i, (v i).coeff 0 • r i
  let f₁ := ∑ i, (v i).coeff 1 • r i
  have hmem (m : ℕ) : (∑ i, (v i).coeff m • r i) ∈ V := by
    apply V.sum_mem
    intro i _
    exact V.smul_mem _ (b i).property
  have hd₀ : f₀.totalDegree ≤ d := (mem_restrictTotalDegree _ _ _).mp (hmem 0)
  have hd₁ : f₁.totalDegree ≤ d := (mem_restrictTotalDegree _ _ _).mp (hmem 1)
  have hn₀ : f₀ ≠ 0 := by
    intro hz
    have hi : LinearIndependent K r := b.linearIndependent.map' V.subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have hh := Fintype.linearIndependent_iff.mp hi (fun i => (v i).coeff 0) hz j
    exact hj (by rwa [← Polynomial.coeff_zero_eq_eval_zero])
  let aq := fun i => (Ideal.Quotient.mk I) (a i)
  let ψ := aeval (R := K) aq
  have hψ (p : MvPolynomial (Fin 2) K) : (Ideal.Quotient.mk I) (aeval a p) = ψ p :=
    comp_aeval_apply a (Ideal.Quotient.mkₐ K I) p
  obtain ⟨h₀, h₁⟩ := plane_deformation_relation_coefficients aq 1
    ((Ideal.Quotient.mk I) l) r v hv
  change ψ f₀ = 0 at h₀
  change ψ f₁ + ψ (pderiv 1 f₀) * (Ideal.Quotient.mk I) l = 0 at h₁
  have hz₀ : aeval a f₀ ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp ((hψ f₀).trans h₀)
  obtain ⟨c, hc⟩ := plane_projection_relation_space I a f hf hker f₀ (by simpa only [hfd] using hd₀) hz₀
  have hcn : c ≠ 0 := by intro hz; apply hn₀; rw [hc, hz, zero_smul]
  rw [hc, Derivation.map_smul, map_smul, smul_mul_assoc] at h₁
  have hs := congrArg (fun x : MvPolynomial τ K ⧸ I => c⁻¹ • x) h₁
  simp only [smul_add, smul_smul, inv_mul_cancel₀ hcn, one_smul, smul_zero] at hs
  let P := -(c⁻¹ • f₁)
  refine ⟨P, ?_, ?_⟩
  · exact (totalDegree_neg _).le.trans ((totalDegree_smul_le _ _).trans hd₁)
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, hψ, hψ]
    simp only [P, map_neg, map_smul, sub_neg_eq_add]
    exact (add_comm _ _).trans hs

end
end AffineCurveCounting
