module

public import AffineCurveCounting.PrimitiveIntegerPolynomial

/-! Primitive models preserve the equation's degree and homogeneous grading,
and integer content removal does not increase coefficient height. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma integer_scalar_factor_ne_zero {σ : Type*} {f g : MvPolynomial σ ℤ} {c : ℤ}
    (hf : f ≠ 0) (he : f = C c * g) : g ≠ 0 := by
  intro hg
  apply hf
  rw [he, hg, mul_zero]

lemma integer_scalar_factor_degree {σ : Type*} {f g : MvPolynomial σ ℤ} {c : ℤ}
    (hf : f ≠ 0) (hc : c ≠ 0) (he : f = C c * g) : g.totalDegree = f.totalDegree := by
  have hg := integer_scalar_factor_ne_zero hf he
  rw [he, totalDegree_mul_of_isDomain (C_eq_zero.not.mpr hc) hg, totalDegree_C, zero_add]

lemma integer_scalar_factor_homogeneous {σ : Type*} {f g : MvPolynomial σ ℤ} {c : ℤ} {d : ℕ}
    (hc : c ≠ 0) (he : f = C c * g) (hf : f.IsHomogeneous d) : g.IsHomogeneous d := by
  have h := homogeneous_multiplier (isHomogeneous_C σ c) (C_eq_zero.not.mpr hc)
    (he ▸ hf) (Nat.zero_le d)
  simpa only [Nat.sub_zero] using h

lemma integer_scalar_factor_coefficient_bound {σ : Type*}
    {f g : MvPolynomial σ ℤ} {c : ℤ} (hc : c ≠ 0) (he : f = C c * g) (m : σ →₀ ℕ) :
    |(g.coeff m : ℝ)| ≤ |(f.coeff m : ℝ)| := by
  have hc1 : (1 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast Int.one_le_abs hc
  rw [he, coeff_C_mul, Int.cast_mul, abs_mul]
  nlinarith [abs_nonneg (g.coeff m : ℝ)]

/-- Every nonzero rational multivariate polynomial has a primitive integer
model differing by a nonzero rational scalar. -/
theorem exists_primitive_integer_model {σ : Type*} (f : MvPolynomial σ ℚ) (hf : f ≠ 0) :
    ∃ (g : MvPolynomial σ ℤ) (a : ℚ), PrimitiveIntegerPolynomial g ∧ a ≠ 0 ∧
      MvPolynomial.map (Int.castRingHom ℚ) g = C a * f := by
  obtain ⟨b, u, hb, hu⟩ := mvPolynomial_integer_multiple f
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hu0 : u ≠ 0 := by
    intro h
    have hz : C (b : ℚ) * f = 0 := by simpa only [h, map_zero] using hu.symm
    exact (mul_ne_zero (C_eq_zero.not.mpr hbQ) hf) hz
  obtain ⟨c, g, hc, hg, he⟩ := exists_primitive_integer_factor u hu0
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  refine ⟨g, (b : ℚ) / c, hg, div_ne_zero hbQ hcQ, ?_⟩
  have hh := congrArg (MvPolynomial.map (Int.castRingHom ℚ)) he
  rw [hu, map_mul, map_C] at hh
  simp only [Int.coe_castRingHom] at hh
  apply mul_left_cancel₀ (C_eq_zero.not.mpr hcQ)
  rw [← mul_assoc, ← C_mul, mul_div_cancel₀ _ hcQ]
  exact hh.symm

lemma rational_scalar_model_degree {σ : Type*} {f : MvPolynomial σ ℚ}
    {g : MvPolynomial σ ℤ} {a : ℚ} (ha : a ≠ 0) (hf : f ≠ 0)
    (he : MvPolynomial.map (Int.castRingHom ℚ) g = C a * f) : g.totalDegree = f.totalDegree := by
  have hd : (MvPolynomial.map (Int.castRingHom ℚ) g).totalDegree = g.totalDegree := by
    unfold totalDegree
    rw [support_map_of_injective _ Int.cast_injective]
  rw [he, totalDegree_mul_of_isDomain (C_eq_zero.not.mpr ha) hf, totalDegree_C, zero_add] at hd
  exact hd.symm

lemma rational_scalar_model_homogeneous {σ : Type*} {f : MvPolynomial σ ℚ}
    {g : MvPolynomial σ ℤ} {a : ℚ} {d : ℕ}
    (he : MvPolynomial.map (Int.castRingHom ℚ) g = C a * f) (hf : f.IsHomogeneous d) :
    g.IsHomogeneous d := by
  apply IsHomogeneous.of_map (f := Int.castRingHom ℚ) Int.cast_injective
  rw [he]
  exact hf.C_mul a

lemma rational_scalar_model_zero_iff {σ : Type*} {f : MvPolynomial σ ℚ}
    {g : MvPolynomial σ ℤ} {a : ℚ} (ha : a ≠ 0)
    (he : MvPolynomial.map (Int.castRingHom ℚ) g = C a * f) (x : σ → ℚ) :
    eval x (MvPolynomial.map (Int.castRingHom ℚ) g) = 0 ↔ eval x f = 0 := by
  rw [he, eval_mul, eval_C]
  exact mul_eq_zero_iff_left ha

lemma rational_scalar_model_irreducible {σ : Type*} {f : MvPolynomial σ ℚ}
    {g : MvPolynomial σ ℤ} {a : ℚ} (ha : a ≠ 0)
    (he : MvPolynomial.map (Int.castRingHom ℚ) g = C a * f) (hf : Irreducible f) :
    Irreducible (MvPolynomial.map (Int.castRingHom ℚ) g) := by
  rw [he]
  exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr ha).map C)).mpr hf

end
end AffineCurveCounting
