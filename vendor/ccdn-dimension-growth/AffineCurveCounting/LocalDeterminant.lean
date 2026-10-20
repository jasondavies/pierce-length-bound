module

public import AffineCurveCounting.Determinant
public import ArithmeticHeights.BombieriVaaler
import all ArithmeticHeights.BombieriVaaler

/-!
# Determinant divisibility from filtered factorizations

Cauchy–Binet turns a weighted factorization into a determinant valuation bound. The
univariate specialization gives the quadratic exponent `s*(s-1)/2` for polynomial
evaluations in one residue class. The passage from a curve's local ring to such a
factorization is a separate, unimplemented part of CCDN §2.
-/

@[expose] public section

namespace AffineCurveCounting

open Matrix

theorem pow_dvd_det_of_weighted_factorization {R : Type*} [CommRing R] {s N : ℕ}
    (U : Matrix (Fin s) (Fin N) R) (V : Matrix (Fin N) (Fin s) R)
    (p : R) (weight : Fin N → ℕ) (e : ℕ)
    (hV : ∀ i j, p ^ weight i ∣ V i j)
    (he : ∀ t : Fin s ↪o Fin N, e ≤ ∑ i, weight (t i)) :
    p ^ e ∣ (U * V).det := by
  classical
  rw [Matrix.det_mul_eq_sum_det_submatrix]
  apply Finset.dvd_sum
  intro S _
  let t := (S : Finset (Fin N)).orderEmbOfFin (Set.powersetCard.card_eq S)
  have hminor := prod_row_factors_dvd_det (V.submatrix t id)
    (fun i => p ^ weight (t i)) (fun i j => hV (t i) j)
  rw [Finset.prod_pow_eq_pow_sum] at hminor
  exact dvd_mul_of_dvd_right ((pow_dvd_pow p (he t)).trans hminor) _

theorem orderEmbedding_value_ge {s N : ℕ} (t : Fin s ↪o Fin N) (i : Fin s) :
    i.val ≤ (t i).val := by
  have hpoint : ∀ j : ℕ, ∀ hj : j < s, j ≤ (t ⟨j, hj⟩).val := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
      intro hj
      have hj' : j < s := by omega
      have hprev := ih hj'
      have hlt := t.strictMono (show (⟨j, hj'⟩ : Fin s) < ⟨j + 1, hj⟩ from by
        change j < j + 1
        omega)
      change (t ⟨j, hj'⟩).val < (t ⟨j + 1, hj⟩).val at hlt
      omega
  exact hpoint i i.isLt

theorem sum_orderEmbedding_values_ge {s N : ℕ} (t : Fin s ↪o Fin N) :
    s * (s - 1) / 2 ≤ ∑ i, (t i).val := by
  calc
    _ = ∑ i : Fin s, i.val := by
      rw [Fin.sum_univ_eq_sum_range (fun j => j), Finset.sum_range_id]
    _ ≤ _ := Finset.sum_le_sum fun i _ => orderEmbedding_value_ge t i

theorem triangular_pow_dvd_det_of_factorization {R : Type*} [CommRing R] {s N : ℕ}
    (U : Matrix (Fin s) (Fin N) R) (V : Matrix (Fin N) (Fin s) R)
    (p : R) (hV : ∀ i j, p ^ i.val ∣ V i j) :
    p ^ (s * (s - 1) / 2) ∣ (U * V).det :=
  pow_dvd_det_of_weighted_factorization U V p (fun i => i.val) _ hV
    sum_orderEmbedding_values_ge

/-- The sequence of weights in which each nonnegative integer occurs `μ` times. -/
def multiplicityExponent (s μ : ℕ) : ℕ := ∑ i : Fin s, i.val / μ

theorem multiplicity_pow_dvd_det_of_factorization {R : Type*} [CommRing R] {s N : ℕ}
    (U : Matrix (Fin s) (Fin N) R) (V : Matrix (Fin N) (Fin s) R)
    (p : R) (μ : ℕ) (hV : ∀ i j, p ^ (i.val / μ) ∣ V i j) :
    p ^ multiplicityExponent s μ ∣ (U * V).det := by
  apply pow_dvd_det_of_weighted_factorization U V p (fun i => i.val / μ) _ hV
  intro t
  exact Finset.sum_le_sum fun i _ => Nat.div_le_div_right (orderEmbedding_value_ge t i)

/-- An explicit quadratic lower estimate for the repeated-weight exponent. -/
theorem multiplicityExponent_lower_bound (s μ : ℕ) (hμ : 0 < μ) :
    s ^ 2 ≤ 2 * μ * (multiplicityExponent s μ + s) := by
  have hi : ∀ i : Fin s, i.val ≤ μ * (i.val / μ) + (μ - 1) := by
    intro i
    have hmod := Nat.mod_lt i.val hμ
    have hdiv := Nat.mod_add_div i.val μ
    omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin s))) => hi i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hid : (∑ i : Fin s, i.val) * 2 = s * (s - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id_mul_two]
  have hμsub : μ - 1 + 1 = μ := by omega
  have hs : s * (s - 1) + s = s ^ 2 := by
    cases s with
    | zero => simp
    | succ s => simp; ring
  unfold multiplicityExponent
  nlinarith

/-- Polynomial evaluations at multiples of `p` have determinant divisible by the
triangular power of `p`. This holds over `ℤ` for every modulus, including nonprimes. -/
theorem triangular_pow_dvd_polynomial_eval_det {s : ℕ}
    (f : Fin s → Polynomial ℤ) (t : Fin s → ℤ) (p : ℤ) :
    p ^ (s * (s - 1) / 2) ∣ (Matrix.of fun i j => (f j).eval (p * t i)).det := by
  classical
  let N := (Finset.univ.sup fun j => (f j).natDegree) + 1
  let U : Matrix (Fin s) (Fin N) ℤ := fun i k => t i ^ k.val
  let V : Matrix (Fin N) (Fin s) ℤ := fun k j => p ^ k.val * (f j).coeff k.val
  have hfac : (Matrix.of fun i j => (f j).eval (p * t i)) = U * V := by
    ext i j
    change (f j).eval (p * t i) = ∑ k : Fin N, t i ^ k.val * (p ^ k.val * (f j).coeff k.val)
    have hdeg : (f j).natDegree < N := by
      exact Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (f j).natDegree) (Finset.mem_univ j))
    rw [Polynomial.eval_eq_sum_range' hdeg]
    rw [Fin.sum_univ_eq_sum_range (fun k => t i ^ k * (p ^ k * (f j).coeff k)) N]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow]
    ring
  rw [hfac]
  exact triangular_pow_dvd_det_of_factorization U V p (fun k j => dvd_mul_right _ _)

/-- The same quadratic divisibility exponent for evaluations in an arbitrary residue class. -/
theorem triangular_pow_dvd_polynomial_eval_det_of_congruent {s : ℕ}
    (f : Fin s → Polynomial ℤ) (x : Fin s → ℤ) (p a : ℤ)
    (hx : ∀ i, p ∣ x i - a) :
    p ^ (s * (s - 1) / 2) ∣ (Matrix.of fun i j => (f j).eval (x i)).det := by
  classical
  choose t ht using hx
  let g : Fin s → Polynomial ℤ := fun j => (f j).comp (Polynomial.X + Polynomial.C a)
  have h := triangular_pow_dvd_polynomial_eval_det g t p
  have heq : (Matrix.of fun i j => (g j).eval (p * t i)) =
      (Matrix.of fun i j => (f j).eval (x i)) := by
    ext i j
    change ((f j).comp (Polynomial.X + Polynomial.C a)).eval (p * t i) = (f j).eval (x i)
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    congr 1
    linarith [ht i]
  rwa [heq] at h

/-- All maximal minors share the residue-class divisibility, so their gcd has it too.
This is the same gcd that appears in the Bombieri–Vaaler bound. -/
theorem triangular_pow_dvd_polynomial_eval_minorGcd {s N : ℕ}
    (f : Fin N → Polynomial ℤ) (x : Fin s → ℤ) (p a : ℤ)
    (hx : ∀ i, p ∣ x i - a) :
    p ^ (s * (s - 1) / 2) ∣ Int.Matrix.minorGcd (Matrix.of fun i j => (f j).eval (x i)) := by
  classical
  unfold Int.Matrix.minorGcd
  apply Finset.dvd_gcd
  intro S _
  rw [Matrix.plucker_row_eq_det_submatrix]
  let t := (S : Finset (Fin N)).orderEmbOfFin (Set.powersetCard.card_eq S)
  exact triangular_pow_dvd_polynomial_eval_det_of_congruent (fun j => f (t j)) x p a hx

end AffineCurveCounting
