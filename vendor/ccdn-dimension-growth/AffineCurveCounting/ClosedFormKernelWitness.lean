module

public import AffineCurveCounting.BivariateCoefficientMatrix
public import AffineCurveCounting.BivariateFactorForms

/-! Reconstruct bounded polynomial closed forms inside the actual matrix
kernel. Two independent forms force the rank drop used by the integer minor. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Matrix

/-- All coefficients outside the strict rectangular grid vanish. -/
def InBivariateGrid {R : Type*} [CommRing R] (d : ℕ) (f : R[X][X]) : Prop :=
  ∀ i j, d ≤ i ∨ d ≤ j → (f.coeff i).coeff j = 0

lemma bivariateGridPolynomial_coeff_zero {R : Type*} [CommRing R] (d : ℕ)
    (v : BivariateGrid d → R) (i j : ℕ) (h : d ≤ i ∨ d ≤ j) :
    ((bivariateGridPolynomial R d v).coeff i).coeff j = 0 := by
  classical
  simp only [bivariateGridPolynomial, LinearMap.coe_mk, AddHom.coe_mk, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k _
  simp only [coeff_monomial]
  split_ifs with he
  · rw [coeff_monomial, ite_eq_right]
    have hk := k.1.isLt
    have hl := k.2.isLt
    omega
  · simp

/-- Coefficient extraction followed by decoding recovers every polynomial
supported on the grid. -/
theorem bivariateGridPolynomial_reconstruct {R : Type*} [CommRing R]
    (d : ℕ) (f : R[X][X]) (hf : InBivariateGrid d f) :
    bivariateGridPolynomial R d (fun i => (f.coeff i.1.val).coeff i.2.val) = f := by
  ext i j
  by_cases hi : i < d
  · by_cases hj : j < d
    · exact bivariateGridPolynomial_coeff _ ⟨i, hi⟩ ⟨j, hj⟩
    · rw [bivariateGridPolynomial_coeff_zero d _ i j (Or.inr (by omega)), hf i j (Or.inr (by omega))]
  · rw [bivariateGridPolynomial_coeff_zero d _ i j (Or.inl (by omega)), hf i j (Or.inl (by omega))]

/-- Every pair supported on the grid comes from an actual coefficient vector. -/
theorem exists_closedFormPair_of_grid {R : Type*} [CommRing R]
    (d : ℕ) (u : R[X][X] × R[X][X]) (hp : InBivariateGrid d u.1)
    (hq : InBivariateGrid d u.2) :
    ∃ v, closedFormPair R d v = u := by
  refine ⟨Sum.elim (fun i => (u.1.coeff i.1.val).coeff i.2.val)
    (fun i => (u.2.coeff i.1.val).coeff i.2.val), ?_⟩
  exact Prod.ext (bivariateGridPolynomial_reconstruct d u.1 hp)
    (bivariateGridPolynomial_reconstruct d u.2 hq)

/-- The gradient itself satisfies the closed-form equation in every field. -/
lemma closedFormOperator_gradient {F : Type*} [Field F] (f : F[X][X]) :
    closedFormOperator f (f.derivative, (bivariateCoefficientDerivative F) f) = 0 := by
  change (bivariateCoefficientDerivative F) f.derivative * f -
    f.derivative * (bivariateCoefficientDerivative F) f -
    ((bivariateCoefficientDerivative F) f).derivative * f +
    (bivariateCoefficientDerivative F) f * f.derivative = 0
  rw [derivative_bivariateCoefficientDerivative]
  ring

/-- Two polynomial solutions, one not a scalar multiple of the other, give
an actual rank drop of at least two. -/
theorem closedForm_rank_drop_of_two_forms {F : Type*} [Field F]
    (d : ℕ) (f : F[X][X]) (u w : F[X][X] × F[X][X])
    (hu₁ : InBivariateGrid d u.1) (hu₂ : InBivariateGrid d u.2)
    (hw₁ : InBivariateGrid d w.1) (hw₂ : InBivariateGrid d w.2)
    (hu : closedFormOperator f u = 0) (hw : closedFormOperator f w = 0)
    (hu0 : u ≠ 0) (hind : ∀ a : F, a • u ≠ w) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  obtain ⟨v, hv⟩ := exists_closedFormPair_of_grid d u hu₁ hu₂
  obtain ⟨z, hz⟩ := exists_closedFormPair_of_grid d w hw₁ hw₂
  let V := (closedFormCoefficientMatrix d f).mulVecLin.ker
  have hvk : v ∈ V := by
    apply (closedFormCoefficientMatrix_kernel d f v).mpr
    rw [hv, hu]
  have hzk : z ∈ V := by
    apply (closedFormCoefficientMatrix_kernel d f z).mpr
    rw [hz, hw]
  let v' : V := ⟨v, hvk⟩
  let z' : V := ⟨z, hzk⟩
  have hv0 : v' ≠ 0 := by
    intro hh
    have hh' : v = 0 := congrArg Subtype.val hh
    apply hu0
    rw [← hv, hh', map_zero]
  have hi : LinearIndependent F ![v', z'] := by
    rw [LinearIndependent.pair_iff' hv0]
    intro a ha
    apply hind a
    have hh : a • v = z := congrArg Subtype.val ha
    rw [← hv, ← hz, ← (closedFormPair F d).map_smul, hh]
  have hdim : 2 ≤ Module.finrank F V := by simpa using hi.fintype_card_le_finrank
  have he := (closedFormCoefficientMatrix d f).mulVecLin.finrank_range_add_finrank_ker
  have hd : Module.finrank F (ClosedFormColumns d → F) = 2 * d ^ 2 := by
    simp [ClosedFormColumns, BivariateGrid, pow_two, two_mul]
  rw [hd] at he
  change (closedFormCoefficientMatrix d f).rank + Module.finrank F V = _ at he
  omega

end
end AffineCurveCounting
