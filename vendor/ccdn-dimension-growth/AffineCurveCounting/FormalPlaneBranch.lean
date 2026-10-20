module

public import AffineCurveCounting.FormalImplicitRoot
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Actual formal branches of plane equations at nonsingular points, in either
coordinate chart. The other coordinate is the parameter X plus its base value. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

/-- Turn coordinate j into a polynomial variable and the other coordinate
into the formal parameter X+a. -/
def formalPlanePolynomial {K : Type*} [CommRing K] (j : Fin 2) (a : K) :
    MvPolynomial (Fin 2) K →+* Polynomial (PowerSeries K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp PowerSeries.C)
    (fun k => if k = j then Polynomial.X else Polynomial.C (PowerSeries.X + PowerSeries.C a))

@[simp] lemma formalPlanePolynomial_C {K : Type*} [CommRing K]
    (j : Fin 2) (a c : K) :
    formalPlanePolynomial j a (MvPolynomial.C c) = Polynomial.C (PowerSeries.C c) := by
  simp [formalPlanePolynomial]

@[simp] lemma formalPlanePolynomial_X {K : Type*} [CommRing K]
    (j k : Fin 2) (a : K) :
    formalPlanePolynomial j a (MvPolynomial.X k) =
      if k = j then Polynomial.X else Polynomial.C (PowerSeries.X + PowerSeries.C a) := by
  simp [formalPlanePolynomial]

lemma formalPlanePolynomial_derivative {K : Type*} [CommRing K]
    (j : Fin 2) (a : K) (f : MvPolynomial (Fin 2) K) :
    (formalPlanePolynomial j a f).derivative = formalPlanePolynomial j a (MvPolynomial.pderiv j f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [formalPlanePolynomial]
  | add f g hf hg => simp [map_add, hf, hg]
  | mul_X f k hf =>
    by_cases h : k = j
    · subst k
      simp [map_mul, Polynomial.derivative_mul, formalPlanePolynomial_X, hf]
      ring
    · simp [map_mul, Polynomial.derivative_mul, formalPlanePolynomial_X, hf, h]
      ring

lemma formalPlanePolynomial_eval {K : Type*} [CommRing K]
    (j : Fin 2) (a : K) (f : MvPolynomial (Fin 2) K) (g : PowerSeries K) :
    (formalPlanePolynomial j a f).eval g =
      MvPolynomial.eval₂ PowerSeries.C (fun k => if k = j then g else PowerSeries.X + PowerSeries.C a) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [formalPlanePolynomial]
  | add f h hf hh => simp [map_add, hf, hh]
  | mul_X f k hf =>
    by_cases h : k = j <;> simp [map_mul, formalPlanePolynomial_X, hf, h]

lemma formalPlanePolynomial_constant_eval {K : Type*} [CommRing K]
    (j : Fin 2) (a b : K) (f : MvPolynomial (Fin 2) K) :
    ((formalPlanePolynomial j a f).map PowerSeries.constantCoeff).eval b =
      MvPolynomial.eval (fun k => if k = j then b else a) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [formalPlanePolynomial]
  | add f h hf hh => simp [map_add, hf, hh]
  | mul_X f k hf =>
    by_cases h : k = j <;> simp [map_mul, formalPlanePolynomial_X, hf, h]

lemma plane_coordinate_cases {K : Type*} (z : Fin 2 → K) (j : Fin 2) :
    (fun k => if k = j then z j else z j.rev) = z := by
  funext k
  fin_cases j <;> fin_cases k <;> simp

/-- A nonzero chosen partial derivative supplies a unique formal branch
through the given point. This works in arbitrary characteristic. -/
theorem exists_unique_formal_plane_branch {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0) (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0) :
    ∃! g : PowerSeries K, PowerSeries.constantCoeff g = z j ∧
      MvPolynomial.eval₂ PowerSeries.C
        (fun k => if k = j then g else PowerSeries.X + PowerSeries.C (z j.rev)) f = 0 := by
  let F := formalPlanePolynomial j (z j.rev) f
  have hroot : (F.map PowerSeries.constantCoeff).eval (z j) = 0 := by
    rw [formalPlanePolynomial_constant_eval, plane_coordinate_cases]
    exact hz
  have hder : (F.derivative.map PowerSeries.constantCoeff).eval (z j) ≠ 0 := by
    dsimp only [F]
    rw [formalPlanePolynomial_derivative, formalPlanePolynomial_constant_eval, plane_coordinate_cases]
    exact hj
  obtain ⟨g, hg, hfg⟩ := exists_formal_simple_root F (z j) hroot hder
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · rwa [formalPlanePolynomial_eval] at hfg
  · intro h hh
    apply formal_simple_root_unique F (z j) hder hh.1 hg
    · rw [formalPlanePolynomial_eval]
      exact hh.2
    · exact hfg

end
end AffineCurveCounting
