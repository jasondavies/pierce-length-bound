module

public import AffineCurveCounting.Interpolation

/-!
# Elementary determinant bounds

The archimedean Gram determinant estimate is the one used in CCDN §3.3. The row-factor
divisibility lemma isolates a basic arithmetic input to determinant lower bounds; it does not
assert the much stronger local multiplicity estimates of CCDN §2.
-/

@[expose] public section

namespace AffineCurveCounting

open Matrix

/-- If row `i` is divisible by `d i`, the product of the row factors divides the determinant. -/
theorem prod_row_factors_dvd_det {R : Type*} [CommRing R] {s : ℕ}
    (A : Matrix (Fin s) (Fin s) R)
    (d : Fin s → R) (h : ∀ i j, d i ∣ A i j) : (∏ i, d i) ∣ A.det := by
  classical
  choose Q hQ using h
  have hA : A = Matrix.of (fun i j => d i * Q i j) := by
    ext i j
    exact hQ i j
  rw [hA]
  exact ⟨(Matrix.of Q).det, Matrix.det_mul_column d (Matrix.of Q)⟩

/-- Bound the Gram determinant by expanding its determinant and bounding each entry.
For monomials of degree at most `M` in a radius-`B` box, take `H = B^M`. -/
theorem abs_gram_det_le {s N : ℕ} (A : Matrix (Fin s) (Fin N) ℝ) {H : ℝ}
    (hH : 0 ≤ H) (hA : ∀ i j, |A i j| ≤ H) :
    |(A * Aᵀ).det| ≤ (s.factorial : ℝ) * ((N : ℝ) * H ^ 2) ^ s := by
  have hentry : ∀ i j, |(A * Aᵀ) i j| ≤ (N : ℝ) * H ^ 2 := by
    intro i j
    calc
      |(A * Aᵀ) i j| = |∑ k, A i k * A j k| := rfl
      _ ≤ ∑ k, |A i k * A j k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin N, H ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul, pow_two]
        exact mul_le_mul (hA i k) (hA j k) (abs_nonneg _) hH
      _ = _ := by simp
  have h := Matrix.det_le (abv := AbsoluteValue.abs) hentry
  simpa [nsmul_eq_mul] using h

/-- Two equal rows modulo an integer modulus force divisibility of the determinant.
Primality is unnecessary for this elementary first-order divisibility statement. -/
theorem modulus_dvd_det_of_congruent_rows {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ)
    (p : ℕ) {i j : Fin s} (hij : i ≠ j) (hrows : ∀ k, (p : ℤ) ∣ A j k - A i k) :
    (p : ℤ) ∣ A.det := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd A.det p).mp
  change (Int.castRingHom (ZMod p)) A.det = 0
  rw [(Int.castRingHom (ZMod p)).map_det]
  apply Matrix.det_zero_of_row_eq hij
  funext k
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub (A i k) (A j k) p).mpr (hrows k)

theorem evaluation_gram_det_le {n N s M : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (points : Fin s → (Fin n → ℤ))
    {B : ℝ} (hB : 1 ≤ B) (hpoints : ∀ i k, |(points i k : ℝ)| ≤ B)
    (hdeg : ∀ j, (mon j).sum (fun _ e => e) ≤ M) :
    let A := (evaluationMatrix mon points).map ((↑) : ℤ → ℝ)
    |(A * Aᵀ).det| ≤ (s.factorial : ℝ) * ((N : ℝ) * (B ^ M) ^ 2) ^ s := by
  apply abs_gram_det_le
  · positivity
  · intro i j
    exact abs_monomial_value_le (mon j) (points i) hB (hpoints i) (hdeg j)

end AffineCurveCounting
