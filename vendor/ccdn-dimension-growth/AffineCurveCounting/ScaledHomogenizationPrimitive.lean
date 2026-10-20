module

public import AffineCurveCounting.ScaledHomogenization

/-! A prime scaling preserves primitive integer equations when it does not
divide the constant coefficient. This is the arithmetic input for affine scaling. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem PrimitiveIntegerPolynomial.scaledHomogenize {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    (hf : PrimitiveIntegerPolynomial f) (d : ℕ) {p : ℕ} (hp : p.Prime)
    (hp0 : ¬ (p : ℤ) ∣ f.coeff 0) :
    PrimitiveIntegerPolynomial (AffineCurveCounting.scaledHomogenize d (p : ℤ) f) := by
  intro c hc
  apply Int.isUnit_iff_natAbs_eq.mpr
  by_contra hunit
  obtain ⟨l, hl, hlc⟩ := Nat.exists_prime_and_dvd hunit
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hld : ∀ m, (l : ℤ) ∣ (AffineCurveCounting.scaledHomogenize d (p : ℤ) f).coeff m :=
    fun m => (Int.natCast_dvd.mpr hlc).trans (hc m)
  have hlp : l ≠ p := by
    intro he
    subst l
    have h := hld (homogenizedExponent d 0)
    rw [scaledHomogenize_coefficient] at h
    simp only [Finsupp.sum_zero_index, pow_zero, one_mul] at h
    exact hp0 h
  have hn : ¬ (l : ℤ) ∣ (p : ℤ) := by
    intro h
    have h' : l ∣ p := by exact_mod_cast h
    exact hlp ((Nat.prime_dvd_prime_iff_eq hl hp).mp h')
  have hcoeff : ∀ m, (l : ℤ) ∣ f.coeff m := by
    intro m
    have h := hld (homogenizedExponent d m)
    rw [scaledHomogenize_coefficient] at h
    rcases hlZ.dvd_or_dvd h with h | h
    · exact False.elim (hn (hlZ.dvd_of_dvd_pow h))
    · exact h
  exact hlZ.not_isUnit (hf l hcoeff)

end
end AffineCurveCounting
