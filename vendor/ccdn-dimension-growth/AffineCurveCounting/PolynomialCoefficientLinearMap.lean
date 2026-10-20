module

public import AffineCurveCounting.PlaneLinearDeformation

/-! Apply a linear functional to the coefficients of a univariate polynomial.
This commutes with evaluation over the scalar field and multiplication by
scalar polynomials, allowing polynomial relations to be encoded by matrices. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial

def coefficientLinearUnivariate {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (φ : A →ₗ[K] K) (p : Polynomial A) : Polynomial K :=
  ∑ n ∈ p.support, monomial n (φ (p.coeff n))

lemma coefficientLinearUnivariate_coeff {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (φ : A →ₗ[K] K) (p : Polynomial A) (n : ℕ) :
    (coefficientLinearUnivariate φ p).coeff n = φ (p.coeff n) := by
  classical
  by_cases hn : n ∈ p.support
  · simp [coefficientLinearUnivariate, coeff_monomial, hn]
  · have hz := notMem_support_iff.mp hn
    simp [coefficientLinearUnivariate, coeff_monomial, hn, hz]

/-- Coefficientwise application of a linear functional. -/
def coefficientLinearUnivariateMap {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (φ : A →ₗ[K] K) : Polynomial A →ₗ[K] Polynomial K where
  toFun := coefficientLinearUnivariate φ
  map_add' p q := by ext n; simp [coefficientLinearUnivariate_coeff]
  map_smul' c p := by ext n; simp [coefficientLinearUnivariate_coeff]

lemma coefficientLinearUnivariate_scalar_mul {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (φ : A →ₗ[K] K) (p : Polynomial K) (q : Polynomial A) :
    coefficientLinearUnivariate φ (p.map (algebraMap K A) * q) =
      p * coefficientLinearUnivariate φ q := by
  ext n
  rw [coefficientLinearUnivariate_coeff, coeff_mul, coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [coeff_map, coefficientLinearUnivariate_coeff]
  simpa [Algebra.smul_def] using φ.map_smul (p.coeff t.1) (q.coeff t.2)

lemma coefficientLinearUnivariate_eval {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (φ : A →ₗ[K] K) (p : Polynomial A) (t : K) :
    (coefficientLinearUnivariate φ p).eval t = φ (p.eval (algebraMap K A t)) := by
  classical
  rw [coefficientLinearUnivariate, Polynomial.eval_finsetSum]
  conv_rhs => rw [p.as_sum_support, Polynomial.eval_finsetSum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [eval_monomial, eval_monomial, ← map_pow]
  have hh := φ.map_smul (t ^ n) (p.coeff n)
  simpa [Algebra.smul_def, mul_comm] using hh.symm

end
end AffineCurveCounting
