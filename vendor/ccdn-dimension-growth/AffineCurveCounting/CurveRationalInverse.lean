module

public import AffineCurveCounting.PrimitivePairReconstruction

/-! Birational projection coordinates admit a rational inverse in the original
coordinate ring. Its denominator cuts out all possible noninjective fibers.
The degree of that denominator is not yet bounded uniformly. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Generation of the actual field gives reconstruction identities modulo the
original ideal, with a denominator that does not vanish identically. -/
theorem exists_curve_reconstruction_identities {K F σ τ : Type*}
    [Field K] [Field F] [Algebra K F] [Fintype τ] [DecidableEq τ]
    (I : Ideal (MvPolynomial τ K)) (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] F)
    (hφ : Function.Injective φ) (a : σ → MvPolynomial τ K)
    (hgen : IntermediateField.adjoin K
      (Set.range (fun j => φ ((Ideal.Quotient.mk I) (a j)))) = ⊤) :
    ∃ Q : MvPolynomial σ K, ∃ P : τ → MvPolynomial σ K,
      aeval a Q ∉ I ∧ ∀ i, aeval a Q * X i - aeval a (P i) ∈ I := by
  let θ := φ.comp (Ideal.Quotient.mkₐ K I)
  have hθ (p : MvPolynomial τ K) : θ p = φ ((Ideal.Quotient.mk I) p) := rfl
  obtain ⟨Q, P, hQ, hP⟩ := exists_common_polynomial_reconstruction
    (fun j => θ (a j)) hgen (fun i => θ (X i))
  have he (p : MvPolynomial σ K) : θ (aeval a p) = aeval (fun j => θ (a j)) p :=
    comp_aeval_apply a θ p
  refine ⟨Q, P, ?_, ?_⟩
  · intro hbad
    apply hQ
    rw [← he, hθ, Ideal.Quotient.eq_zero_iff_mem.mpr hbad, map_zero]
  · intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hφ
    rw [map_zero]
    change θ (aeval a Q * X i - aeval a (P i)) = 0
    rw [map_sub, map_mul, he, he, hP, sub_self]

/-- Polynomial reconstruction gives injectivity at every source point where
the denominator is nonzero. -/
theorem projection_injective_off_reconstruction {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K)
    (Q : MvPolynomial σ K) (P : τ → MvPolynomial σ K)
    (hP : ∀ i, aeval a Q * X i - aeval a (P i) ∈ I)
    (z w : τ → K) (hz : ∀ g ∈ I, eval z g = 0) (hw : ∀ g ∈ I, eval w g = 0)
    (hQ : eval z (aeval a Q) ≠ 0)
    (he : (fun j => eval z (a j)) = (fun j => eval w (a j))) : z = w := by
  have hev (p : MvPolynomial σ K) : eval z (aeval a p) = eval w (aeval a p) := by
    change eval z (eval₂ C a p) = eval w (eval₂ C a p)
    rw [← eval_assoc, ← eval_assoc]
    change eval (fun j => eval z (a j)) p = eval (fun j => eval w (a j)) p
    rw [he]
  funext i
  apply mul_left_cancel₀ hQ
  have hz' := hz _ (hP i)
  have hw' := hw _ (hP i)
  simp only [eval_sub, eval_mul, eval_X, sub_eq_zero] at hz' hw'
  rw [hz', hev (P i), hev Q]
  exact hw'.symm

end
end AffineCurveCounting
