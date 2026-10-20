module

public import AffineCurveCounting.HomogeneousChart

/-! Integral scaled homogenization. The point (h,x) on the homogeneous model
corresponds to the original integer affine point x, without dividing coordinates. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma homogenizedExponent_injective {n : ℕ} (d : ℕ) :
    Function.Injective (homogenizedExponent (n := n) d) := by
  intro m k h
  simpa only [chartExponent_homogenizedExponent] using congrArg chartExponent h

def scaledHomogenize {R : Type*} [CommRing R] {n : ℕ} (d : ℕ) (h : R)
    (f : MvPolynomial (Fin n) R) : MvPolynomial (Fin (n + 1)) R :=
  ∑ m ∈ f.support, monomial (homogenizedExponent d m) (h ^ m.sum (fun _ e => e) * f.coeff m)

lemma scaledHomogenize_coefficient {R : Type*} [CommRing R] {n : ℕ}
    (d : ℕ) (h : R) (f : MvPolynomial (Fin n) R) (m : Fin n →₀ ℕ) :
    (scaledHomogenize d h f).coeff (homogenizedExponent d m) =
      h ^ m.sum (fun _ e => e) * f.coeff m := by
  classical
  by_cases hm : m ∈ f.support
  · simp [scaledHomogenize, coeff_monomial, (homogenizedExponent_injective d).eq_iff, hm]
  · have hz := notMem_support_iff.mp hm
    simp [scaledHomogenize, coeff_monomial, (homogenizedExponent_injective d).eq_iff, hm, hz]

lemma scaledHomogenize_homogeneous {R : Type*} [CommRing R] {n d : ℕ}
    (h : R) (f : MvPolynomial (Fin n) R) (hf : f.totalDegree ≤ d) :
    (scaledHomogenize d h f).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro m hm
  exact isHomogeneous_monomial _ (homogenizedExponent_degree m ((le_totalDegree hm).trans hf))

lemma homogenizedExponent_value {R : Type*} [CommRing R] {n : ℕ}
    (d : ℕ) (h : R) (x : Fin n → R) (m : Fin n →₀ ℕ) :
    (homogenizedExponent d m).prod (fun j e => ((Fin.cons h x : Fin (n + 1) → R) j) ^ e) =
      h ^ (d - m.sum (fun _ e => e)) * m.prod (fun j e => x j ^ e) := by
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ,
    Finsupp.prod_fintype _ _ (by simp)]
  rfl

/-- Exact evaluation at the scaled homogenizing coordinate. -/
theorem scaledHomogenize_eval {R : Type*} [CommRing R] {n d : ℕ}
    (h : R) (f : MvPolynomial (Fin n) R) (hf : f.totalDegree ≤ d) (x : Fin n → R) :
    eval (Fin.cons h x) (scaledHomogenize d h f) = h ^ d * eval x f := by
  classical
  rw [scaledHomogenize, map_sum]
  conv_rhs => rw [f.as_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [eval_monomial, eval_monomial, homogenizedExponent_value]
  calc
    _ = (h ^ m.sum (fun _ e => e) * h ^ (d - m.sum (fun _ e => e))) *
      (f.coeff m * m.prod (fun j e => x j ^ e)) := by ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le ((le_totalDegree hm).trans hf)]

lemma scaledHomogenize_ne_zero {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (d : ℕ) {h : R} (hh : h ≠ 0) {f : MvPolynomial (Fin n) R} (hf : f ≠ 0) :
    scaledHomogenize d h f ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  intro hz
  have hc := scaledHomogenize_coefficient d h f m
  have he : h ^ m.sum (fun _ e => e) * f.coeff m = 0 := by simpa [hz] using hc.symm
  exact (mul_ne_zero (pow_ne_zero _ hh) hm) he

/-- A scaling factor at least one does not decrease any original coefficient. -/
lemma scaledHomogenize_integer_coefficient_lower {n : ℕ} (d : ℕ) {h : ℤ} (hh : 1 ≤ h)
    (f : MvPolynomial (Fin n) ℤ) (m : Fin n →₀ ℕ) :
    |(f.coeff m : ℝ)| ≤ |((scaledHomogenize d h f).coeff (homogenizedExponent d m) : ℝ)| := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  rw [scaledHomogenize_coefficient, Int.cast_mul, Int.cast_pow, abs_mul, abs_pow,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]
  have hp := one_le_pow₀ (n := m.sum (fun _ e => e)) hhR
  nlinarith [abs_nonneg (f.coeff m : ℝ)]

/-- A highest-degree nonzero coefficient gains the full factor h^d. -/
theorem exists_scaledHomogenize_top_coefficient {n : ℕ} (f : MvPolynomial (Fin n) ℤ)
    (hf : f ≠ 0) {h : ℤ} (hh : 1 ≤ h) :
    ∃ m : Fin n →₀ ℕ, m.sum (fun _ e => e) = f.totalDegree ∧
      (h : ℝ) ^ f.totalDegree ≤
        |((scaledHomogenize f.totalDegree h f).coeff (homogenizedExponent f.totalDegree m) : ℝ)| := by
  obtain ⟨m, hm, hdeg⟩ := f.support.exists_mem_eq_sup (support_nonempty.mpr hf)
    (fun m => m.sum (fun _ e => e))
  have hm0 : f.coeff m ≠ 0 := mem_support_iff.mp hm
  have hdegree : m.sum (fun _ e => e) = f.totalDegree := hdeg.symm
  refine ⟨m, hdegree, ?_⟩
  have hcoef : (1 : ℝ) ≤ |(f.coeff m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  rw [scaledHomogenize_coefficient, hdegree, Int.cast_mul, Int.cast_pow, abs_mul, abs_pow,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]
  nlinarith [show 0 ≤ (h : ℝ) ^ f.totalDegree by positivity]

end
end AffineCurveCounting
