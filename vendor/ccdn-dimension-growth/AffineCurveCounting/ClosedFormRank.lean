module

public import AffineCurveCounting.BivariateCoefficientMatrix

/-! Rank forced by the characteristic-zero closed-form classification. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Matrix Submodule

/-- For a normalized irreducible equation the entire coefficient kernel
maps into the one-dimensional span of the gradient. -/
theorem closedForm_kernel_image_le_gradient
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] (d : ℕ)
    (f : F[X][X]) (hf : Irreducible f) (hm : f.Monic) (hdeg : f.degree = d) :
    LinearMap.range ((closedFormPair F d).domRestrict
      (closedFormCoefficientMatrix d f).mulVecLin.ker) ≤
      F ∙ (f.derivative, (bivariateCoefficientDerivative F) f) := by
  rintro u ⟨v, rfl⟩
  have hv := (closedFormCoefficientMatrix_kernel d f v.val).mp (LinearMap.mem_ker.mp v.property)
  let p := (closedFormPair F d v.val).1
  let q := (closedFormPair F d v.val).2
  have hp : p.degree < f.degree := by
    rw [hdeg]
    exact bivariateGridPolynomial_degree_lt _
  have hq : q.degree < f.degree := by
    rw [hdeg]
    exact bivariateGridPolynomial_degree_lt _
  have he : (bivariateCoefficientDerivative F) p * f - p * (bivariateCoefficientDerivative F) f =
      q.derivative * f - q * f.derivative := by
    change (bivariateCoefficientDerivative F) p * f - p * (bivariateCoefficientDerivative F) f -
      q.derivative * f + q * f.derivative = 0 at hv
    linear_combination hv
  obtain ⟨a, ha, hb⟩ := bivariate_closed_form_eq_gradient f p q hf hm hp hq he
  apply Submodule.mem_span_singleton.mpr
  refine ⟨a, ?_⟩
  apply Prod.ext
  · change a • f.derivative = p
    simpa only [Algebra.smul_def, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using ha.symm
  · change a • (bivariateCoefficientDerivative F) f = q
    simpa only [Algebra.smul_def, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using hb.symm

/-- No more than one independent coefficient vector solves the closed-form
matrix for an irreducible normalized equation. -/
theorem closedForm_kernel_finrank_le_one
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] (d : ℕ)
    (f : F[X][X]) (hf : Irreducible f) (hm : f.Monic) (hdeg : f.degree = d) :
    Module.finrank F (closedFormCoefficientMatrix d f).mulVecLin.ker ≤ 1 := by
  let U := (closedFormCoefficientMatrix d f).mulVecLin.ker
  let ψ := (closedFormPair F d).domRestrict U
  have hi : Function.Injective ψ := (closedFormPair_injective d).comp Subtype.val_injective
  have he := LinearMap.finrank_range_of_inj hi
  have hl := Submodule.finrank_mono (closedForm_kernel_image_le_gradient d f hf hm hdeg)
  have hs : Module.finrank F (F ∙ (f.derivative, (bivariateCoefficientDerivative F) f)) ≤ 1 := by
    simpa using finrank_span_le_card (R := F) ({(f.derivative, (bivariateCoefficientDerivative F) f)} : Set _)
  exact he ▸ hl.trans hs

/-- The matrix on the 2*d² actual unknown coefficients has rank at least
2*d²-1. No finite-field or Noether theorem is assumed in this statement. -/
theorem closedForm_coefficient_rank_lower
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] (d : ℕ)
    (f : F[X][X]) (hf : Irreducible f) (hm : f.Monic) (hdeg : f.degree = d) :
    2 * d ^ 2 ≤ (closedFormCoefficientMatrix d f).rank + 1 := by
  have he := (closedFormCoefficientMatrix d f).mulVecLin.finrank_range_add_finrank_ker
  have hk := closedForm_kernel_finrank_le_one d f hf hm hdeg
  have hdim : Module.finrank F (ClosedFormColumns d → F) = 2 * d ^ 2 := by
    simp [ClosedFormColumns, BivariateGrid, pow_two, two_mul]
  rw [hdim] at he
  change (closedFormCoefficientMatrix d f).rank + _ = _ at he
  omega

end
end AffineCurveCounting
