module

public import AffineCurveCounting.IntegerGridInterpolation
public import AffineCurveCounting.ShearNormalization
public import AffineCurveCounting.PlaneBadPrimes

/-! A coefficient-height witness on the bounded integer plane grid. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial

lemma bivariatePolynomialEquiv_eval {R : Type*} [CommRing R]
    (f : MvPolynomial (Fin 2) R) (x y : R) :
    (Polynomial.map (Polynomial.evalRingHom y) (bivariatePolynomialEquiv R f)).eval x =
      MvPolynomial.eval ![x, y] f := by
  have he : (Polynomial.evalRingHom x).comp
      ((Polynomial.mapRingHom (Polynomial.evalRingHom y)).comp (bivariatePolynomialEquiv R).toRingHom) =
      MvPolynomial.eval ![x, y] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [bivariatePolynomialEquiv_C]
    · intro i
      fin_cases i <;> simp [bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
  exact RingHom.congr_fun he f

theorem bivariate_coefficient_bound_of_integer_grid (f : ℝ[X][X]) {d : ℕ}
    (hd : bivariateTotalDegree f ≤ d) {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ x y : ℕ, x ≤ d → y ≤ d →
      |(Polynomial.map (Polynomial.evalRingHom (y : ℝ)) f).eval (x : ℝ)| ≤ H) (i j : ℕ) :
    |(f.coeff i).coeff j| ≤ ((d : ℝ) + 1) ^ (2 * (d + 1)) * H := by
  have hcoeff (y : ℕ) (hy : y ≤ d) :
      |(f.coeff i).eval (y : ℝ)| ≤ ((d : ℝ) + 1) ^ (d + 1) * H := by
    have hh := polynomial_coefficient_bound_of_integer_grid
      (Polynomial.map (Polynomial.evalRingHom (y : ℝ)) f)
      ((Polynomial.natDegree_map_le).trans ((bivariate_natDegree_le_totalDegree f).trans hd))
      hH (fun x hx => heval x y hx hy) i
    simpa only [coeff_map, coe_evalRingHom] using hh
  have hh := polynomial_coefficient_bound_of_integer_grid (f.coeff i)
    ((bivariate_coefficient_natDegree_le_totalDegree f i).trans hd)
    (show 0 ≤ ((d : ℝ) + 1) ^ (d + 1) * H by positivity) hcoeff j
  convert hh using 1
  rw [show 2 * (d + 1) = (d + 1) * 2 by omega, pow_mul, pow_two]
  ring

theorem plane_coefficient_bound_of_integer_grid (f : MvPolynomial (Fin 2) ℝ) {d : ℕ}
    (hd : f.totalDegree ≤ d) {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ x y : ℕ, x ≤ d → y ≤ d → |MvPolynomial.eval ![(x : ℝ), (y : ℝ)] f| ≤ H)
    (m : Fin 2 →₀ ℕ) : |f.coeff m| ≤ ((d : ℝ) + 1) ^ (2 * (d + 1)) * H := by
  have hh := bivariate_coefficient_bound_of_integer_grid (bivariatePolynomialEquiv ℝ f)
    (by simpa only [bivariateTotalDegree_equiv] using hd) hH
    (fun x y hx hy => by rw [bivariatePolynomialEquiv_eval]; exact heval x y hx hy) (m 0) (m 1)
  rwa [bivariatePolynomialEquiv_coeff, ← bivariate_exponent_eq m] at hh

/-- One grid point simultaneously controls every coefficient. -/
theorem exists_plane_grid_height_witness (f : MvPolynomial (Fin 2) ℝ) {d : ℕ}
    (hd : f.totalDegree ≤ d) :
    ∃ x y : ℕ, x ≤ d ∧ y ≤ d ∧ ∀ m,
      |f.coeff m| ≤ ((d : ℝ) + 1) ^ (2 * (d + 1)) *
        |MvPolynomial.eval ![(x : ℝ), (y : ℝ)] f| := by
  classical
  let S := Finset.range (d + 1) ×ˢ Finset.range (d + 1)
  have hS : S.Nonempty := ⟨(0, 0), by simp [S]⟩
  obtain ⟨p, hp, hmax⟩ := S.exists_max_image
    (fun p : ℕ × ℕ => |MvPolynomial.eval ![(p.1 : ℝ), (p.2 : ℝ)] f|) hS
  have hp' : p.1 ≤ d ∧ p.2 ≤ d := by
    simpa only [S, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] using hp
  refine ⟨p.1, p.2, hp'.1, hp'.2, ?_⟩
  apply plane_coefficient_bound_of_integer_grid f hd (abs_nonneg _)
  intro x y hx hy
  exact hmax (x, y) (by simp only [S, Finset.mem_product, Finset.mem_range]; omega)

/-- The integer version also supplies a nonzero value for every nonzero
plane equation. -/
theorem exists_integer_plane_grid_height_witness (f : MvPolynomial (Fin 2) ℤ)
    (hf : f ≠ 0) {d : ℕ} (hd : f.totalDegree ≤ d) :
    ∃ x y : ℕ, x ≤ d ∧ y ≤ d ∧ MvPolynomial.eval ![(x : ℤ), (y : ℤ)] f ≠ 0 ∧ ∀ m,
      |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (2 * (d + 1)) *
        |(MvPolynomial.eval ![(x : ℤ), (y : ℤ)] f : ℝ)| := by
  let fR := MvPolynomial.map (Int.castRingHom ℝ) f
  have hdeg : fR.totalDegree ≤ d := by
    dsimp only [fR]
    unfold MvPolynomial.totalDegree
    rw [MvPolynomial.support_map_of_injective _ Int.cast_injective]
    exact hd
  obtain ⟨x, y, hx, hy, h⟩ := exists_plane_grid_height_witness fR hdeg
  have he : MvPolynomial.eval ![(x : ℝ), (y : ℝ)] fR =
      (MvPolynomial.eval ![(x : ℤ), (y : ℤ)] f : ℝ) := by
    have hh := MvPolynomial.map_eval (Int.castRingHom ℝ) ![(x : ℤ), (y : ℤ)] f
    change (Int.castRingHom ℝ) (MvPolynomial.eval ![(x : ℤ), (y : ℤ)] f) =
      MvPolynomial.eval (fun i => ((![(x : ℤ), (y : ℤ)] i : ℤ) : ℝ)) fR at hh
    have hv : (fun i => ((![(x : ℤ), (y : ℤ)] i : ℤ) : ℝ)) = ![(x : ℝ), (y : ℝ)] := by
      funext i
      fin_cases i <;> simp
    simpa only [hv, Int.coe_castRingHom] using hh.symm
  have hc (m) : |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (2 * (d + 1)) *
      |(MvPolynomial.eval ![(x : ℤ), (y : ℤ)] f : ℝ)| := by
    simpa only [fR, MvPolynomial.coeff_map, Int.coe_castRingHom, ← he] using h m
  refine ⟨x, y, hx, hy, ?_, hc⟩
  intro hz
  apply hf
  apply MvPolynomial.ext
  intro m
  have hh := hc m
  rw [hz, Int.cast_zero, abs_zero, mul_zero] at hh
  have heq := abs_nonpos_iff.mp hh
  exact Int.cast_injective (α := ℝ) (by simpa using heq)

lemma integer_plane_eval_real_map (f : MvPolynomial (Fin 2) ℤ) (x y : ℕ) :
    MvPolynomial.eval ![(x : ℝ), (y : ℝ)] (MvPolynomial.map (Int.castRingHom ℝ) f) =
      (MvPolynomial.eval ![(x : ℤ), (y : ℤ)] f : ℝ) := by
  have hh := MvPolynomial.map_eval (Int.castRingHom ℝ) ![(x : ℤ), (y : ℤ)] f
  change (Int.castRingHom ℝ) (MvPolynomial.eval ![(x : ℤ), (y : ℤ)] f) =
    MvPolynomial.eval (fun i => ((![(x : ℤ), (y : ℤ)] i : ℤ) : ℝ))
      (MvPolynomial.map (Int.castRingHom ℝ) f) at hh
  have hv : (fun i => ((![(x : ℤ), (y : ℤ)] i : ℤ) : ℝ)) = ![(x : ℝ), (y : ℝ)] := by
    funext i
    fin_cases i <;> simp
  simpa only [hv, Int.coe_castRingHom] using hh.symm

theorem integer_plane_coefficient_bound_of_grid (f : MvPolynomial (Fin 2) ℤ) {d : ℕ}
    (hd : f.totalDegree ≤ d) {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ x y : ℕ, x ≤ d → y ≤ d → |(MvPolynomial.eval ![(x : ℤ), (y : ℤ)] f : ℝ)| ≤ H)
    (m : Fin 2 →₀ ℕ) : |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (2 * (d + 1)) * H := by
  have hdR : (MvPolynomial.map (Int.castRingHom ℝ) f).totalDegree ≤ d := by
    unfold MvPolynomial.totalDegree
    rw [MvPolynomial.support_map_of_injective _ Int.cast_injective]
    exact hd
  have h := plane_coefficient_bound_of_integer_grid (MvPolynomial.map (Int.castRingHom ℝ) f)
    hdR hH (fun x y hx hy => by rw [integer_plane_eval_real_map]; exact heval x y hx hy) m
  simpa only [MvPolynomial.coeff_map, Int.coe_castRingHom] using h

end
end AffineCurveCounting
