module

public import AffineCurveCounting.ClosedFormReducibility
public import AffineCurveCounting.ClosedFormRank

/-! Scaling the defining equation by a nonzero constant preserves the matrix
rank. This permits monic normalization over fields without enlarging integer
coefficients or clearing new denominators. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Matrix

lemma closedFormOperator_smul_equation {R : Type*} [CommRing R]
    (a : R) (f : R[X][X]) (u : R[X][X] × R[X][X]) :
    closedFormOperator (a • f) u = a • closedFormOperator f u := by
  change _ * (a • f) - _ * (bivariateCoefficientDerivative R) (a • f) -
    _ * (a • f) + _ * (a • f).derivative = a • (_ - _ - _ + _)
  rw [(bivariateCoefficientDerivative R).map_smul, derivative_smul]
  simp only [mul_smul_comm, smul_sub, smul_add]

lemma closedFormCoefficientMatrix_smul {R : Type*} [CommRing R]
    (a : R) (d : ℕ) (f : R[X][X]) :
    closedFormCoefficientMatrix d (a • f) = a • closedFormCoefficientMatrix d f := by
  classical
  ext i j
  change (bivariateCoefficients R (closedFormOperator (a • f)
    (closedFormPair R d (Pi.single j 1)))) i =
    a * (bivariateCoefficients R (closedFormOperator f
      (closedFormPair R d (Pi.single j 1)))) i
  rw [closedFormOperator_smul_equation, (bivariateCoefficients R).map_smul]
  rfl

lemma closedForm_rank_smul {F : Type*} [Field F] (a : F) (ha : a ≠ 0)
    (d : ℕ) (f : F[X][X]) :
    (closedFormCoefficientMatrix d (a • f)).rank = (closedFormCoefficientMatrix d f).rank := by
  rw [closedFormCoefficientMatrix_smul]
  exact Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero ha)

lemma bivariate_smul_eq_constant_mul {R : Type*} [CommRing R] (a : R) (f : R[X][X]) :
    a • f = C (C a) * f := by
  simp only [Algebra.smul_def, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

lemma bivariate_irreducible_smul_iff {F : Type*} [Field F]
    (a : F) (ha : a ≠ 0) (f : F[X][X]) : Irreducible (a • f) ↔ Irreducible f := by
  rw [bivariate_smul_eq_constant_mul]
  have hu : IsUnit (C (C a) : F[X][X]) := ((isUnit_iff_ne_zero.mpr ha).map C).map C
  exact (associated_unit_mul_left f (C (C a)) hu).irreducible_iff

lemma bivariateTotalDegree_smul_le {R : Type*} [CommRing R] (a : R) (f : R[X][X]) :
    bivariateTotalDegree (a • f) ≤ bivariateTotalDegree f := by
  unfold bivariateTotalDegree
  rw [map_smul]
  exact MvPolynomial.totalDegree_smul_le _ _

/-- Normalize over the coefficient field, so no integer denominators need to
be cleared in the original coefficient matrix. -/
lemma bivariate_monic_normalize {F : Type*} [Field F]
    (a : F) (ha : a ≠ 0) (f : F[X][X]) (hl : f.leadingCoeff = C a) :
    (a⁻¹ • f).Monic := by
  rw [bivariate_smul_eq_constant_mul]
  change (C (C a⁻¹) * f).leadingCoeff = 1
  rw [leadingCoeff_mul, leadingCoeff_C, hl, ← map_mul, inv_mul_cancel₀ ha, map_one]

/-- The characteristic-zero rank lower bound needs only a nonzero constant
outer leading coefficient, not an integer monic equation. -/
theorem closedForm_rank_lower_of_constant_leading
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (d : ℕ) (a : F) (ha : a ≠ 0) (f : F[X][X])
    (hl : f.leadingCoeff = C a) (hf : Irreducible f) (hdeg : f.natDegree = d) :
    2 * d ^ 2 ≤ (closedFormCoefficientMatrix d f).rank + 1 := by
  have hm := bivariate_monic_normalize a ha f hl
  have hi := (bivariate_irreducible_smul_iff a⁻¹ (inv_ne_zero ha) f).mpr hf
  have hd : (a⁻¹ • f).degree = d := by
    rw [degree_eq_natDegree hm.ne_zero, natDegree_smul f (inv_ne_zero ha), hdeg]
  have hr := closedForm_coefficient_rank_lower d _ hi hm hd
  rw [closedForm_rank_smul _ (inv_ne_zero ha)] at hr
  exact hr

/-- The characteristic-p reducibility criterion likewise only needs a nonzero
constant outer leading coefficient. -/
theorem closedForm_rank_drop_of_constant_leading
    {F : Type*} [Field F] (p d : ℕ) [CharP F p] (hd : 0 < d) (hdp : d < p)
    (a : F) (ha : a ≠ 0) (f : F[X][X])
    (hl : f.leadingCoeff = C a) (hred : ¬Irreducible f)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  have hm := bivariate_monic_normalize a ha f hl
  have hi : ¬Irreducible (a⁻¹ • f) := fun h =>
    hred ((bivariate_irreducible_smul_iff a⁻¹ (inv_ne_zero ha) f).mp h)
  have hr := closedForm_rank_drop_of_not_irreducible p d hd hdp (a⁻¹ • f) hm hi
    ((natDegree_smul f (inv_ne_zero ha)).trans hdeg)
    ((bivariateTotalDegree_smul_le _ _).trans htotal)
  rw [closedForm_rank_smul _ (inv_ne_zero ha)] at hr
  exact hr

end
end AffineCurveCounting
