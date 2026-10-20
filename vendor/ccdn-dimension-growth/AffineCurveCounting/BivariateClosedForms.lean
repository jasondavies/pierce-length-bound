module

public import AffineCurveCounting.RationalClosedForms

/-! The characteristic-zero closed-form criterion on actual bivariate
polynomials. Gauss's lemma and rational differentiation discharge the
fraction-field and differential-field hypotheses. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Differential
open scoped Polynomial.Bivariate
attribute [local instance] rationalDifferential

/-- Differentiate the inner variable of a bivariate polynomial. -/
def bivariateCoefficientDerivative (F : Type*) [CommRing F] :
    Derivation F F[X][X] F[X][X] :=
  PolynomialModule.equivPolynomialSelf.compDer Polynomial.derivative'.mapCoeffs

@[simp]
lemma coeff_bivariateCoefficientDerivative {F : Type*} [CommRing F] (p : F[X][X]) (n : ℕ) :
    ((bivariateCoefficientDerivative F) p).coeff n = (p.coeff n).derivative := rfl

lemma bivariateCoefficientDerivative_map {F : Type*} [Field F] (p : F[X][X]) :
    ((bivariateCoefficientDerivative F) p).map (algebraMap F[X] (RatFunc F)) =
      Differential.mapCoeffs (p.map (algebraMap F[X] (RatFunc F))) := by
  ext n
  simp only [coeff_map, coeff_bivariateCoefficientDerivative, Differential.coeff_mapCoeffs]
  exact (rationalDerivative_polynomial (p.coeff n)).symm

/-- Over an algebraically closed field of characteristic zero, a monic
irreducible bivariate equation has only constant-gradient closed forms
within the strict outer-variable degree bounds. -/
theorem bivariate_closed_form_eq_gradient
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (f p q : F[X][X]) (hf : Irreducible f) (hm : f.Monic)
    (hpdeg : p.degree < f.degree) (hqdeg : q.degree < f.degree)
    (hclosed : (bivariateCoefficientDerivative F) p * f - p * (bivariateCoefficientDerivative F) f =
      q.derivative * f - q * f.derivative) :
    ∃ a : F, p = C (C a) * f.derivative ∧
      q = C (C a) * (bivariateCoefficientDerivative F) f := by
  let φ := algebraMap F[X] (RatFunc F)
  have hinj := RatFunc.algebraMap_injective F
  have hfR : Irreducible (f.map φ) := (hm.irreducible_iff_irreducible_map_fraction_map).mp hf
  have hpR : (p.map φ).degree < (f.map φ).degree := by
    simpa only [φ, degree_map_eq_of_injective hinj] using hpdeg
  have hqR : (q.map φ).degree < (f.map φ).degree := by
    simpa only [φ, degree_map_eq_of_injective hinj] using hqdeg
  have he : Differential.mapCoeffs (p.map φ) * f.map φ - p.map φ * Differential.mapCoeffs (f.map φ) =
      (q.map φ).derivative * f.map φ - q.map φ * (f.map φ).derivative := by
    simp only [derivative_map]
    dsimp only [φ]
    rw [← bivariateCoefficientDerivative_map, ← bivariateCoefficientDerivative_map]
    simpa only [Polynomial.map_sub, Polynomial.map_mul] using congrArg (Polynomial.map φ) hclosed
  obtain ⟨a, hp, hq⟩ := rational_closed_form_eq_gradient (f.map φ) (p.map φ) (q.map φ)
    hfR (hm.map φ) hpR hqR he
  refine ⟨a, ?_, ?_⟩
  · apply Polynomial.map_injective φ hinj
    simpa only [Polynomial.map_mul, Polynomial.map_C, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C, derivative_map, φ] using hp
  · apply Polynomial.map_injective φ hinj
    simpa only [Polynomial.map_mul, Polynomial.map_C, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C, φ, bivariateCoefficientDerivative_map] using hq

end
end AffineCurveCounting
