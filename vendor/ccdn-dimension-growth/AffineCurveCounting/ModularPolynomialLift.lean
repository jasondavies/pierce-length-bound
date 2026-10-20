module

public import AffineCurveCounting.SingularTangent

/-! Coefficientwise integer lifts preserve homogeneous weights and origin-ideal
powers. Reduction modulo p has exactly the coefficientwise divisibility kernel. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def modularPolynomialLift {σ : Type*} {p : ℕ} (f : MvPolynomial σ (ZMod p)) :
    MvPolynomial σ ℤ := ∑ e ∈ f.support, monomial e (f.coeff e).val

lemma coeff_modularPolynomialLift {σ : Type*} {p : ℕ}
    (f : MvPolynomial σ (ZMod p)) (e : σ →₀ ℕ) :
    (modularPolynomialLift f).coeff e = (f.coeff e).val := by
  classical
  simp only [modularPolynomialLift, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with he
  · rfl
  · have hc : f.coeff e = 0 := by simpa only [mem_support_iff, not_not] using he
    rw [hc, ZMod.val_zero, Nat.cast_zero]

lemma map_modularPolynomialLift {σ : Type*} {p : ℕ} [NeZero p]
    (f : MvPolynomial σ (ZMod p)) : map (Int.castRingHom (ZMod p)) (modularPolynomialLift f) = f := by
  ext e
  simp only [coeff_map, coeff_modularPolynomialLift, Int.coe_castRingHom,
    Int.cast_natCast, ZMod.natCast_zmod_val]

lemma modularPolynomialLift_homogeneous {σ : Type*} {p k : ℕ}
    (f : MvPolynomial σ (ZMod p)) (hf : f.IsHomogeneous k) :
    (modularPolynomialLift f).IsHomogeneous k := by
  intro e he
  have hfe : f.coeff e ≠ 0 := by
    intro h
    exact he (by simp only [coeff_modularPolynomialLift, h, ZMod.val_zero, Nat.cast_zero])
  exact hf hfe

lemma modularPolynomialLift_mem_origin_power {σ : Type*} {p k : ℕ}
    (f : MvPolynomial σ (ZMod p)) (hf : f ∈ idealOfVars σ (ZMod p) ^ k) :
    modularPolynomialLift f ∈ idealOfVars σ ℤ ^ k := by
  rw [mem_pow_idealOfVars_iff'] at hf ⊢
  intro e he
  rw [coeff_modularPolynomialLift, hf e he, ZMod.val_zero, Nat.cast_zero]

lemma map_mod_prime_eq_zero_iff {σ : Type*} (p : ℕ) (f : MvPolynomial σ ℤ) :
    map (Int.castRingHom (ZMod p)) f = 0 ↔ C (p : ℤ) ∣ f := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h e
    have he := congrArg (fun q : MvPolynomial σ (ZMod p) => q.coeff e) h
    simp only [coeff_map, Int.coe_castRingHom, AddMonoidAlgebra.coeff_zero] at he
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he
  · intro h
    ext e
    simp only [coeff_map, Int.coe_castRingHom, AddMonoidAlgebra.coeff_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h e)

end
end AffineCurveCounting
