/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendCoordinates
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Irreducibility from a nonsingular quadratic part

A ternary quadratic with nonzero Hessian determinant cannot factor into two
affine linear polynomials. The argument works over arbitrary fields.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

open MvPolynomial

noncomputable section

/-- The Hessian evaluated at the origin. -/
def hessianAtZero {K : Type*} [CommRing K] (f : MvPolynomial (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => eval (fun _ => 0) (pderiv i (pderiv j f))

lemma pderiv_pderiv_eq_zero {K : Type*} [CommRing K] {f : MvPolynomial (Fin 3) K}
    (hd : f.totalDegree ≤ 1) (i j : Fin 3) : pderiv i (pderiv j f) = 0 := by
  classical
  ext m
  rw [coeff_pderiv, coeff_pderiv]
  have hz : f.coeff (m + Finsupp.single i 1 + Finsupp.single j 1) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    change f.totalDegree < (m + Finsupp.single i 1 + Finsupp.single j 1).sum (fun _ e => e)
    simp only [Finsupp.sum_fintype _ (fun (_ : Fin 3) (e : ℕ) => e) (fun _ => rfl),
      Finsupp.add_apply, Finset.sum_add_distrib]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    omega
  simp [hz]

lemma hessian_eq_zero_of_degree_le_one {K : Type*} [CommRing K]
    {f : MvPolynomial (Fin 3) K} (hd : f.totalDegree ≤ 1) : hessianAtZero f = 0 := by
  ext i j
  simp [hessianAtZero, pderiv_pderiv_eq_zero hd]

lemma hessian_mul_affine_det {K : Type*} [CommRing K] {f g : MvPolynomial (Fin 3) K}
    (hf : f.totalDegree ≤ 1) (hg : g.totalDegree ≤ 1) :
    (hessianAtZero (f * g)).det = 0 := by
  have hentry : hessianAtZero (f * g) = Matrix.of fun i j =>
      eval (fun _ => 0) (pderiv i f) * eval (fun _ => 0) (pderiv j g) +
      eval (fun _ => 0) (pderiv j f) * eval (fun _ => 0) (pderiv i g) := by
    ext i j
    simp [hessianAtZero, pderiv_pderiv_eq_zero hf,
      pderiv_pderiv_eq_zero hg, mul_comm]
  rw [hentry, Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  ring

/-- A ternary polynomial of total degree at most two with nonsingular Hessian is irreducible. -/
theorem irreducible_of_hessian_det_ne_zero {K : Type*} [Field K]
    {f : MvPolynomial (Fin 3) K} (hd : f.totalDegree ≤ 2)
    (hh : (hessianAtZero f).det ≠ 0) : Irreducible f := by
  have hf0 : f ≠ 0 := by
    intro hz
    subst f
    have he := hessian_eq_zero_of_degree_le_one (f := (0 : MvPolynomial (Fin 3) K)) (by simp)
    exact hh (by rw [he, Matrix.det_zero])
  have hnonconst : f.totalDegree ≠ 0 := by
    intro hz
    have he := hessian_eq_zero_of_degree_le_one (f := f) (by omega)
    rw [he, Matrix.det_zero] at hh
    exact hh rfl
  refine ⟨?_, ?_⟩
  · intro hu
    exact hnonconst (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
  · intro g h hgh
    have hg0 : g ≠ 0 := by intro hz; rw [hz, zero_mul] at hgh; exact hf0 hgh
    have hh0 : h ≠ 0 := by intro hz; rw [hz, mul_zero] at hgh; exact hf0 hgh
    by_cases hg : g.totalDegree = 0
    · left
      have he := totalDegree_eq_zero_iff_eq_C.mp hg
      rw [he]
      apply IsUnit.map C
      apply isUnit_iff_ne_zero.mpr
      intro hz
      apply hg0
      rw [he, hz, map_zero]
    by_cases hh' : h.totalDegree = 0
    · right
      have he := totalDegree_eq_zero_iff_eq_C.mp hh'
      rw [he]
      apply IsUnit.map C
      apply isUnit_iff_ne_zero.mpr
      intro hz
      apply hh0
      rw [he, hz, map_zero]
    have hsum : g.totalDegree + h.totalDegree ≤ 2 := by
      rw [hgh, totalDegree_mul_of_isDomain hg0 hh0] at hd
      exact hd
    have he := hessian_mul_affine_det (f := g) (g := h) (by omega) (by omega)
    exact (hh (hgh ▸ he)).elim

/-- A diagonal quadratic plus a rank-one quadratic and an arbitrary linear part. -/
def ternaryQuadratic {K : Type*} [CommRing K] (a b c l0 l1 l2 : K) :
    MvPolynomial (Fin 3) K :=
  C a * X 0 ^ 2 + C b * X 1 ^ 2 + C c * X 2 ^ 2 +
    (C a * X 0 + C b * X 1 + C c * X 2) ^ 2 +
    (C l0 * X 0 + C l1 * X 1 + C l2 * X 2)

lemma linear_form_degree_le {K : Type*} [Field K] (a b c : K) :
    (C a * X 0 + C b * X 1 + C c * X 2 : MvPolynomial (Fin 3) K).totalDegree ≤ 1 := by
  have hterm : ∀ (a : K) (j : Fin 3), (C a * X j).totalDegree ≤ 1 := by
    intro a j
    simpa using totalDegree_mul (C a) (X j)
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le (hterm a 0) (hterm b 1))) (hterm c 2))

lemma ternaryQuadratic_degree_le {K : Type*} [Field K] (a b c l0 l1 l2 : K) :
    (ternaryQuadratic a b c l0 l1 l2).totalDegree ≤ 2 := by
  have hterm : ∀ (a : K) (j : Fin 3), (C a * X j ^ 2 : MvPolynomial (Fin 3) K).totalDegree ≤ 2 := by
    intro a j
    calc
      _ ≤ (C a : MvPolynomial (Fin 3) K).totalDegree +
          (X j ^ 2 : MvPolynomial (Fin 3) K).totalDegree := totalDegree_mul _ _
      _ = 2 := by rw [totalDegree_C, totalDegree_X_pow]
  have hdiag : (C a * X 0 ^ 2 + C b * X 1 ^ 2 + C c * X 2 ^ 2 :
      MvPolynomial (Fin 3) K).totalDegree ≤ 2 :=
    (totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le (hterm a 0) (hterm b 1))) (hterm c 2))
  have hsquare := (totalDegree_pow
    (C a * X 0 + C b * X 1 + C c * X 2 : MvPolynomial (Fin 3) K) 2).trans
      (Nat.mul_le_mul_left 2 (linear_form_degree_le a b c))
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le hdiag hsquare))
    ((linear_form_degree_le l0 l1 l2).trans (by omega)))

lemma ternaryQuadratic_hessian_det {K : Type*} [CommRing K] (a b c l0 l1 l2 : K) :
    (hessianAtZero (ternaryQuadratic a b c l0 l1 l2)).det =
      8 * a * b * c * (1 + a + b + c) := by
  simp [hessianAtZero, ternaryQuadratic, Matrix.det_fin_three, Pi.single_apply]
  norm_num only [map_ofNat]
  ring

/-- The exact algebraic shape of the eliminated quadratic. -/
lemma lineQuadratic_eq_ternary {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) :
    lineQuadratic (C ρ) (C u) (C v) (C ρ') (C u') (C v') (X 0) (X 1) (X 2) =
      ternaryQuadratic (-ρ - u) (u - v) (v - 1)
        (ρ - (-ρ - u) - ρ' - (-ρ - u) * (v - 1 - v'))
        ((-ρ - u) - (u - v) + ρ' + u' - (u - v) * (v - 1 - v'))
        ((u - v) - (v - 1) - u' + v' - (v - 1) * (v - 1 - v')) := by
  simp [lineQuadratic, lineNodes, lineGaps, fourthNode, coeffs, ternaryQuadratic,
    Fin.sum_univ_succ]
  ring

/-- Irreducibility of the eliminated quadratic over any field where the four
coefficient factors are nonzero. In particular this applies over the complex numbers. -/
theorem lineQuadratic_irreducible {K : Type*} [Field K] [CharZero K]
    (ρ u v ρ' u' v' : K) (hρ : ρ ≠ 0) (hρu : ρ + u ≠ 0)
    (huv : u - v ≠ 0) (hv : v - 1 ≠ 0) :
    Irreducible (lineQuadratic (C ρ) (C u) (C v) (C ρ') (C u') (C v')
      (X 0) (X 1) (X 2) : MvPolynomial (Fin 3) K) := by
  rw [lineQuadratic_eq_ternary]
  apply irreducible_of_hessian_det_ne_zero (ternaryQuadratic_degree_le _ _ _ _ _ _)
  rw [ternaryQuadratic_hessian_det]
  have h1 : -ρ - u ≠ 0 := by simpa [neg_add_rev, sub_eq_add_neg, add_comm] using neg_ne_zero.mpr hρu
  have h2 : 1 + (-ρ - u) + (u - v) + (v - 1) = -ρ := by ring
  rw [h2]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h1) huv) hv)
    (neg_ne_zero.mpr hρ)

/-- Absolute irreducibility of the actual orbit quadratic, witnessed over ℂ. -/
theorem orbit_lineQuadratic_irreducible {a b i : ℕ} (hba : b < a)
    (hi : i + 6 < P a b) :
    Irreducible (lineQuadratic
      (C (patternRho a b i : ℂ)) (C (patternU a b i : ℂ)) (C (patternV a b i : ℂ))
      (C (patternRho a b (i + 1) : ℂ)) (C (patternU a b (i + 1) : ℂ))
      (C (patternV a b (i + 1) : ℂ)) (X 0) (X 1) (X 2) : MvPolynomial (Fin 3) ℂ) := by
  obtain ⟨hρ, hu, hv⟩ := orbit_pattern_signs hba hi
  apply lineQuadratic_irreducible
  · exact_mod_cast hρ.ne'
  · exact_mod_cast (show patternRho a b i + patternU a b i ≠ 0 by linarith)
  · exact_mod_cast (show patternU a b i - patternV a b i ≠ 0 by linarith)
  · exact_mod_cast (show patternV a b i - 1 ≠ 0 by linarith)

end
end PierceLengthBound.FixedDividend
