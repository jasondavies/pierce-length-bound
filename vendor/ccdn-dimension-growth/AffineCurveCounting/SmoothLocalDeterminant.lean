module

public import AffineCurveCounting.BlockDeterminant
import all ArithmeticHeights.BombieriVaaler
public import Mathlib.Algebra.Polynomial.Derivative

/-! Local determinant divisibility at nonsingular integral plane-curve points.
Finite polynomial Newton approximation supplies the local parameter; no p-adic
implicit-function theorem is assumed. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Matrix

/-- Divided differences agree with the derivative modulo the argument difference. -/
lemma polynomial_divided_difference {R : Type*} [CommRing R]
    (f : R[X]) (y z : R) :
    ∃ q : R, f.eval y - f.eval z = (y - z) * q ∧
      y - z ∣ q - f.derivative.eval z := by
  have hd : X - C z ∣ f - C (f.eval z) := by
    rw [dvd_iff_isRoot]
    simp [IsRoot]
  obtain ⟨g, hg⟩ := hd
  have he := congrArg (Polynomial.eval y) hg
  simp only [eval_sub, eval_C, eval_mul, eval_X] at he
  have hder := congrArg (fun p : R[X] => p.derivative.eval z) hg
  simp only [derivative_sub, derivative_C, sub_zero, derivative_mul,
    derivative_X, derivative_sub, eval_add, eval_mul, eval_sub,
    eval_X, eval_C, sub_self, zero_mul, one_mul, add_zero] at hder
  refine ⟨g.eval y, he, ?_⟩
  rw [hder]
  exact Polynomial.sub_dvd_eval_sub y z g

def planeEval (f : Polynomial (Polynomial ℤ)) (x y : ℤ) : ℤ :=
  (f.map (Polynomial.evalRingHom x)).eval y

lemma planeEval_substitute (f : Polynomial (Polynomial ℤ)) (g : Polynomial ℤ) (x : ℤ) :
    (f.eval g).eval x = planeEval f x (g.eval x) :=
  (Polynomial.eval_map_apply (Polynomial.evalRingHom x) g).symm

lemma planeEval_congr (f : Polynomial (Polynomial ℤ)) {p x y a b : ℤ}
    (hx : p ∣ x - a) (hy : p ∣ y - b) : p ∣ planeEval f x y - planeEval f a b := by
  have h1 : p ∣ planeEval f x y - planeEval f x b :=
    hy.trans (Polynomial.sub_dvd_eval_sub y b (f.map (Polynomial.evalRingHom x)))
  have h2 : p ∣ planeEval f x b - planeEval f a b := by
    have h := hx.trans (Polynomial.sub_dvd_eval_sub x a (f.eval (C b)))
    simpa only [planeEval_substitute, eval_C] using h
  convert dvd_add h1 h2 using 1; ring

/-- One polynomial Newton step improves simultaneous congruences at all points
in the same nonsingular residue class. -/
lemma plane_newton_step (f : Polynomial (Polynomial ℤ)) (g : Polynomial ℤ)
    {p a b u x y : ℤ} {k : ℕ} (hk : 1 ≤ k)
    (hunit : p ∣ 1 - u * planeEval f.derivative a b)
    (hx : p ∣ x - a) (hy : p ∣ y - b) (hf : planeEval f x y = 0)
    (hg : p ^ k ∣ y - g.eval x) :
    p ^ (k + 1) ∣ y - (g - C u * f.eval g).eval x := by
  let F := f.map (Polynomial.evalRingHom x)
  obtain ⟨q, hq, hd⟩ := polynomial_divided_difference F y (g.eval x)
  have hpg : p ∣ y - g.eval x := by simpa only [pow_one] using (pow_dvd_pow p hk).trans hg
  have hgb : p ∣ g.eval x - b := by
    convert dvd_sub hy hpg using 1; ring
  have hder : F.derivative.eval (g.eval x) = planeEval f.derivative x (g.eval x) := by
    simp only [F, planeEval, Polynomial.derivative_map]
  have hdiff : p ∣ q - planeEval f.derivative a b := by
    have h1 := hpg.trans hd
    rw [hder] at h1
    have h2 := planeEval_congr f.derivative hx hgb
    convert dvd_add h1 h2 using 1; ring
  have hq1 : p ∣ 1 - u * q := by
    have hh := dvd_mul_of_dvd_right hdiff u
    convert dvd_sub hunit hh using 1; ring
  have he : y - (g - C u * f.eval g).eval x = (y - g.eval x) * (1 - u * q) := by
    simp only [eval_sub, eval_mul, eval_C, planeEval_substitute]
    change planeEval f x y - planeEval f x (g.eval x) = _ at hq
    rw [hf] at hq
    linear_combination -u * hq
  rw [he, pow_succ]
  exact mul_dvd_mul hg hq1

/-- A nonsingular residue class has a common polynomial parameter approximation
of every finite p-adic precision, for all integral points of the curve at once. -/
theorem smooth_plane_polynomial_approximation (f : Polynomial (Polynomial ℤ))
    (p a b : ℤ) (hunit : IsCoprime p (planeEval f.derivative a b)) (k : ℕ) :
    ∃ g : Polynomial ℤ, ∀ x y : ℤ, p ∣ x - a → p ∣ y - b →
      planeEval f x y = 0 → p ^ k ∣ y - g.eval x := by
  obtain ⟨v, u, hu⟩ := hunit
  have hunit' : p ∣ 1 - u * planeEval f.derivative a b := by
    refine ⟨v, ?_⟩
    linear_combination -hu
  have h : ∀ n : ℕ, ∃ g : Polynomial ℤ, ∀ x y : ℤ, p ∣ x - a → p ∣ y - b →
      planeEval f x y = 0 → p ^ (n + 1) ∣ y - g.eval x := by
    intro n
    induction n with
    | zero => exact ⟨C b, fun x y hx hy hf => by simpa using hy⟩
    | succ n ih =>
      obtain ⟨g, hg⟩ := ih
      refine ⟨g - C u * f.eval g, fun x y hx hy hf => ?_⟩
      exact plane_newton_step f g (by omega) hunit' hx hy hf (hg x y hx hy hf)
  obtain ⟨g, hg⟩ := h k
  exact ⟨g, fun x y hx hy hf =>
    (pow_dvd_pow p (Nat.le_succ k)).trans (hg x y hx hy hf)⟩


/-- Entrywise congruence implies determinant congruence, for every modulus. -/
lemma dvd_det_sub_of_dvd_entries {s : ℕ} (A B : Matrix (Fin s) (Fin s) ℤ)
    (m : ℤ) (h : ∀ i j, m ∣ A i j - B i j) : m ∣ A.det - B.det := by
  let I : Ideal ℤ := Ideal.span {m}
  let φ := Ideal.Quotient.mk I
  have he : A.map φ = B.map φ := by
    ext i j
    apply sub_eq_zero.mp
    change φ (A i j) - φ (B i j) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h i j))
  apply Ideal.mem_span_singleton.mp
  change A.det - B.det ∈ I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change φ (A.det - B.det) = 0
  rw [map_sub, φ.map_det, φ.map_det]
  change (A.map φ).det - (B.map φ).det = 0
  rw [he, sub_self]

/-- The full triangular determinant exponent for evaluations of arbitrary
polynomials on a single nonsingular plane-curve residue class. -/
theorem triangular_pow_dvd_smooth_plane_eval_det {s : ℕ}
    (f : Polynomial (Polynomial ℤ)) (g : Fin s → Polynomial (Polynomial ℤ))
    (x y : Fin s → ℤ) (p a b : ℤ)
    (hunit : IsCoprime p (planeEval f.derivative a b))
    (hx : ∀ i, p ∣ x i - a) (hy : ∀ i, p ∣ y i - b)
    (hf : ∀ i, planeEval f (x i) (y i) = 0) :
    p ^ (s * (s - 1) / 2) ∣ (Matrix.of fun i j => planeEval (g j) (x i) (y i)).det := by
  let e := s * (s - 1) / 2
  obtain ⟨q, hq⟩ := smooth_plane_polynomial_approximation f p a b hunit e
  let A : Matrix (Fin s) (Fin s) ℤ := fun i j => planeEval (g j) (x i) (y i)
  let B : Matrix (Fin s) (Fin s) ℤ := fun i j => ((g j).eval q).eval (x i)
  have he : p ^ e ∣ A.det - B.det := by
    apply dvd_det_sub_of_dvd_entries
    intro i j
    have hd := (hq (x i) (y i) (hx i) (hy i) (hf i)).trans
      (Polynomial.sub_dvd_eval_sub (y i) (q.eval (x i))
        ((g j).map (Polynomial.evalRingHom (x i))))
    simpa only [A, B, planeEval_substitute, planeEval] using hd
  have hb : p ^ e ∣ B.det :=
    triangular_pow_dvd_polynomial_eval_det_of_congruent (fun j => (g j).eval q) x p a hx
  change p ^ e ∣ A.det
  convert dvd_add he hb using 1
  ring

/-- All maximal minors of the smooth evaluation matrix satisfy the same local
valuation bound. -/
theorem triangular_pow_dvd_smooth_plane_eval_minorGcd {s N : ℕ}
    (f : Polynomial (Polynomial ℤ)) (g : Fin N → Polynomial (Polynomial ℤ))
    (x y : Fin s → ℤ) (p a b : ℤ)
    (hunit : IsCoprime p (planeEval f.derivative a b))
    (hx : ∀ i, p ∣ x i - a) (hy : ∀ i, p ∣ y i - b)
    (hf : ∀ i, planeEval f (x i) (y i) = 0) :
    p ^ (s * (s - 1) / 2) ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => planeEval (g j) (x i) (y i)) := by
  classical
  unfold Int.Matrix.minorGcd
  apply Finset.dvd_gcd
  intro S _
  rw [Matrix.plucker_row_eq_det_submatrix]
  exact triangular_pow_dvd_smooth_plane_eval_det f _ x y p a b hunit hx hy hf

end
end AffineCurveCounting
