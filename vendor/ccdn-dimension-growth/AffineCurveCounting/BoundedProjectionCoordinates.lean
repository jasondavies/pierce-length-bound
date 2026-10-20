module

public import AffineCurveCounting.CurvePrimitivePair

/-! Integral coordinates and explicit box control for the bounded primitive
pair. This does not yet assert preservation of curve degree or finite fibers. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma momentCoordinate_eval {K : Type*} [CommRing K] {n : ℕ}
    (k : ℕ) (z : Fin n → K) :
    eval z (momentCoordinate K n k) = ∑ j : Fin n, (k : K) ^ j.val * z j := by
  simp only [momentCoordinate, map_sum, map_mul, eval_C, eval_X]

/-- The actual integral linear form has coefficient-uniform polynomial height. -/
theorem momentCoordinate_height {n d k : ℕ} (hk : k ≤ n * d ^ 2)
    {B : ℝ} (z : IntPoint n) (hz : ∀ j, |(z j : ℝ)| ≤ B) :
    |(eval z (momentCoordinate ℤ n k) : ℝ)| ≤
      n * ((n : ℝ) * d ^ 2 + 1) ^ n * B := by
  rw [momentCoordinate_eval, Int.cast_sum]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  have hM : (1 : ℝ) ≤ n * (d : ℝ) ^ 2 + 1 := by
    have hh : (0 : ℝ) ≤ n * (d : ℝ) ^ 2 := by positivity
    linarith
  have hkM : (k : ℝ) ≤ n * (d : ℝ) ^ 2 + 1 := by exact_mod_cast (hk.trans (Nat.le_succ _))
  calc
    _ ≤ ∑ j : Fin n, |(k : ℝ) ^ j.val * (z j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, ((n : ℝ) * d ^ 2 + 1) ^ n * B := by
      apply Finset.sum_le_sum
      intro j _
      have hp : (k : ℝ) ^ j.val ≤ ((n : ℝ) * d ^ 2 + 1) ^ n := by
        calc
          _ ≤ ((n : ℝ) * d ^ 2 + 1) ^ j.val := by gcongr
          _ ≤ _ := pow_le_pow_right₀ hM (Nat.le_of_lt j.isLt)
      simp only [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      exact mul_le_mul hp (hz j) (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The primitive pair evaluated on integral points. -/
def momentProjection {n : ℕ} (j : Fin n) (k : ℕ) (z : IntPoint n) : IntPoint 2 :=
  ![z j, eval z (momentCoordinate ℤ n k)]

/-- Uniform box control for both coordinates, without denominators. -/
theorem momentProjection_box {n d k : ℕ} (j : Fin n) (hk : k ≤ n * d ^ 2)
    {B : ℝ} (hB : 0 ≤ B) {z : IntPoint n} (hz : z ∈ integerBox n B) :
    momentProjection j k z ∈ integerBox 2
      ((1 + n * ((n : ℝ) * d ^ 2 + 1) ^ n) * B) := by
  apply mem_integerBox.mpr
  intro i
  have hb : ∀ j, |(z j : ℝ)| ≤ B := mem_integerBox.mp hz
  have hnon : (0 : ℝ) ≤ n * ((n : ℝ) * d ^ 2 + 1) ^ n * B := by positivity
  fin_cases i
  · change |(z j : ℝ)| ≤ _
    nlinarith only [hb j, hnon]
  · change |(eval z (momentCoordinate ℤ n k) : ℝ)| ≤ _
    have hh := momentCoordinate_height hk z hb
    nlinarith only [hh, hB]

end
end AffineCurveCounting
