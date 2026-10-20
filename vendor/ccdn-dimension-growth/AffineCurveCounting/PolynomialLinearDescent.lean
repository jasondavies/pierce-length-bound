module

public import AffineCurveCounting.Bezout
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Linear coefficient descent of a polynomial over a field extension.
A nonzero polynomial vanishing at base-field points has a nonzero base-field
polynomial of no larger degree vanishing at every one of those points. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def coefficientLinearPolynomial {k K : Type*} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (φ : K →ₗ[k] k) (f : MvPolynomial (Fin n) K) : MvPolynomial (Fin n) k :=
  ∑ m ∈ f.support, monomial m (φ (f.coeff m))

lemma coefficientLinearPolynomial_coeff {k K : Type*} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (φ : K →ₗ[k] k) (f : MvPolynomial (Fin n) K) (m : Fin n →₀ ℕ) :
    (coefficientLinearPolynomial φ f).coeff m = φ (f.coeff m) := by
  classical
  by_cases hm : m ∈ f.support
  · simp [coefficientLinearPolynomial, coeff_monomial, hm]
  · have hz := notMem_support_iff.mp hm
    simp [coefficientLinearPolynomial, coeff_monomial, hm, hz]

lemma coefficientLinearPolynomial_degree {k K : Type*} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (φ : K →ₗ[k] k) (f : MvPolynomial (Fin n) K) :
    (coefficientLinearPolynomial φ f).totalDegree ≤ f.totalDegree := by
  apply totalDegree_finsetSum_le
  intro m hm
  exact (totalDegree_monomial_le _ _).trans (le_totalDegree hm)

lemma coefficientLinearPolynomial_eval {k K : Type*} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (φ : K →ₗ[k] k) (f : MvPolynomial (Fin n) K) (x : Fin n → k) :
    eval x (coefficientLinearPolynomial φ f) = φ (eval (algebraMap k K ∘ x) f) := by
  classical
  rw [coefficientLinearPolynomial, map_sum]
  conv_rhs => rw [f.as_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [eval_monomial, eval_monomial]
  have hp : m.prod (fun j e => ((algebraMap k K ∘ x) j) ^ e) =
      algebraMap k K (m.prod (fun j e => x j ^ e)) := by
    rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
    simp only [map_prod, map_pow, Function.comp_apply]
  rw [hp, mul_comm (f.coeff m)]
  simpa only [smul_eq_mul, Algebra.smul_def, mul_comm] using
    (φ.map_smul (m.prod (fun j e => x j ^ e)) (f.coeff m)).symm

/-- Descent preserves every zero whose coordinates lie in the base field. -/
theorem exists_nonzero_polynomial_linear_descent {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : f ≠ 0) :
    ∃ g : MvPolynomial (Fin n) k, g ≠ 0 ∧ g.totalDegree ≤ f.totalDegree ∧
      ∀ x : Fin n → k, eval (algebraMap k K ∘ x) f = 0 → eval x g = 0 := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hm
  refine ⟨coefficientLinearPolynomial φ f, ?_, coefficientLinearPolynomial_degree φ f, ?_⟩
  · intro he
    have hh := coefficientLinearPolynomial_coeff φ f m
    have hz : φ (f.coeff m) = 0 := by simpa [he] using hh.symm
    exact hφ hz
  · intro x hx
    rw [coefficientLinearPolynomial_eval, hx, map_zero]

end
end AffineCurveCounting
