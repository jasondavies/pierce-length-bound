module

public import AffineCurveCounting.ScaledBoxExponent
public import AffineCurveCounting.ScalingPrime

/-! The affine exponent 1/d with the scaling prime constructed from Mertens.
This branch assumes a nonzero constant coefficient of small logarithmic height;
the sharp finite-field count is still an explicit geometric hypothesis. -/

@[expose] public section
namespace AffineCurveCounting
open Real

theorem plane_finite_count_small_constant_coefficient
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f))
    (hd : 0 < f.totalDegree) (hf0 : f.coeff 0 ≠ 0)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hz : ∀ i, MvPolynomial.eval (z i) f = 0)
    {B C : ℝ} (hB : scalingPrimeRatio ≤ B)
    (hheight : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio)
    (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (hcount : ∀ ℓ : ℕ, ℓ.Prime → 27 * (f.totalDegree : ℝ) ^ 4 < (ℓ : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) f) →
      (Nat.card (PlaneResidue f ℓ) : ℝ) ≤
        ℓ + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt ℓ) :
    (t : ℝ) ≤
      (38 + 8 * Real.exp (heightDeterminantError C + 20) +
        2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 * scalingPrimeRatio) *
      (f.totalDegree : ℝ) ^ 3 * B ^ (1 / (f.totalDegree : ℝ)) *
        (Real.log B + f.totalDegree) := by
  obtain ⟨p, hp, hlo, hhi, hnd⟩ := exists_scaling_prime hB hf0 hheight
  have hA := scalingPrimeRatio_one_le
  have hA0 : 0 < scalingPrimeRatio := by linarith
  have hBp : B ≤ scalingPrimeRatio * p := by
    have h := (div_lt_iff₀ hA0).mp hlo
    nlinarith
  exact scaled_plane_finite_count_one_over_degree f hprim hir hd hp hnd z hinj hz
    hA (hA.trans hB) hhi hBp hbox hC hcount

end AffineCurveCounting
