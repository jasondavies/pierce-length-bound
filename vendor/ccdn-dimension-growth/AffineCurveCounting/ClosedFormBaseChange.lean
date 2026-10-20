module

public import AffineCurveCounting.BivariateCoefficientMatrix

/-! The closed-form coefficient matrix commutes with coefficient ring maps,
including passage from integers to characteristic zero and reduction modulo p. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Matrix

/-- Apply a ring map to both levels of bivariate coefficients. -/
def bivariateMap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    R[X][X] →+* S[X][X] := Polynomial.mapRingHom (Polynomial.mapRingHom φ)

@[simp]
lemma bivariateMap_coeff {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X][X]) (i j : ℕ) :
    ((bivariateMap φ f).coeff i).coeff j = φ ((f.coeff i).coeff j) := by
  simp [bivariateMap]

lemma bivariateMap_derivative {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X][X]) :
    bivariateMap φ f.derivative = (bivariateMap φ f).derivative := by
  exact (Polynomial.derivative_map _ _).symm

lemma bivariateMap_coefficientDerivative {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X][X]) :
    bivariateMap φ ((bivariateCoefficientDerivative R) f) =
      (bivariateCoefficientDerivative S) (bivariateMap φ f) := by
  apply Polynomial.ext
  intro i
  simp [bivariateMap, Polynomial.derivative_map]

lemma bivariateMap_gridPolynomial {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : ℕ) (v : BivariateGrid d → R) :
    bivariateMap φ (bivariateGridPolynomial R d v) =
      bivariateGridPolynomial S d (fun i => φ (v i)) := by
  simp [bivariateGridPolynomial, bivariateMap]

lemma bivariateMap_closedFormOperator {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X][X]) (u : R[X][X] × R[X][X]) :
    bivariateMap φ (closedFormOperator f u) =
      closedFormOperator (bivariateMap φ f) (bivariateMap φ u.1, bivariateMap φ u.2) := by
  change bivariateMap φ (_ - _ - _ + _) = _
  simp only [map_add, map_sub, map_mul, bivariateMap_coefficientDerivative,
    bivariateMap_derivative, closedFormOperator, LinearMap.coe_mk, AddHom.coe_mk]

/-- Matrix entries base-change exactly; no injectivity or characteristic
hypothesis on the coefficient map is needed. -/
theorem closedFormCoefficientMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : ℕ) (f : R[X][X]) :
    (closedFormCoefficientMatrix d f).map φ =
      closedFormCoefficientMatrix d (bivariateMap φ f) := by
  classical
  ext i j
  change φ ((bivariateCoefficients R (closedFormOperator f
    (closedFormPair R d (Pi.single j 1)))) i) =
    (bivariateCoefficients S (closedFormOperator (bivariateMap φ f)
      (closedFormPair S d (Pi.single j 1)))) i
  change φ (((closedFormOperator f (closedFormPair R d (Pi.single j 1))).coeff i.1).coeff i.2) = _
  rw [← bivariateMap_coeff, bivariateMap_closedFormOperator]
  suffices hp : (bivariateMap φ (closedFormPair R d (Pi.single j 1)).1,
      bivariateMap φ (closedFormPair R d (Pi.single j 1)).2) =
      closedFormPair S d (Pi.single j 1) by rw [hp]; rfl
  apply Prod.ext
  · change bivariateMap φ (bivariateGridPolynomial R d _) = bivariateGridPolynomial S d _
    rw [bivariateMap_gridPolynomial]
    congr 1
    ext k
    simp [Pi.single_apply]
  · change bivariateMap φ (bivariateGridPolynomial R d _) = bivariateGridPolynomial S d _
    rw [bivariateMap_gridPolynomial]
    congr 1
    ext k
    simp [Pi.single_apply]

end
end AffineCurveCounting
