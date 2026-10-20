module

public import AffineCurveCounting.AffineNonzeroConstant
public import AffineCurveCounting.AffineTranslationCount

/-! All affine scaling, coefficient-height and zero-constant-term reductions
for primitive absolutely irreducible plane equations. The sharp finite-field
estimate is the sole external counting hypothesis in the resulting bound. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Real

lemma curveBound_translation_radius {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    curveBound d (((d : ℝ) + 1) * B) ≤ 2 * Real.exp 1 * curveBound d B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hB0 : 0 < B := by linarith
  have hdplus : (0 : ℝ) < d + 1 := by positivity
  have hlogB := Real.log_nonneg hB
  have hlogd : Real.log ((d : ℝ) + 1) ≤ d := by
    have h := Real.log_le_sub_one_of_pos hdplus
    linarith
  have hpow : ((d : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hdplus, mul_one_div]
    apply Real.exp_le_exp.mpr
    exact (div_le_one hd0).mpr hlogd
  have hlog : Real.log (((d : ℝ) + 1) * B) + d ≤ 2 * (Real.log B + d) := by
    rw [Real.log_mul hdplus.ne' hB0.ne']
    linarith
  unfold curveBound
  rw [Real.mul_rpow hdplus.le hB0.le]
  have hh := mul_le_mul hpow hlog
    (by
      have hR : 1 ≤ ((d : ℝ) + 1) * B := one_le_mul_of_one_le_of_one_le (by linarith) hB
      have := Real.log_nonneg hR
      positivity)
    (Real.exp_pos 1).le
  have ht := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) by positivity)
  convert ht using 1 <;> ring

/-- For primitive absolutely irreducible integer plane equations, all analytic
and coordinate reductions are proved. The sharp finite-field point estimate
remains explicit; no prime choice or coefficient-height assumptions remain. -/
theorem plane_finite_count_of_sharp_residue_bound
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) (hd : 0 < f.totalDegree)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z) (hz : ∀ i, eval (z i) f = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (hcount : ∀ ℓ : ℕ, ℓ.Prime → 27 * (f.totalDegree : ℝ) ^ 4 < (ℓ : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) f) →
      (Nat.card (PlaneResidue f ℓ) : ℝ) ≤ ℓ + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt ℓ) :
    (t : ℝ) ≤ (2 * Real.exp 1 * affineNonzeroConstantBound C) * curveBound f.totalDegree B := by
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
  obtain ⟨a, ha, ha0⟩ := exists_bounded_translation_nonzero_constant f hf0
  let q := affineTranslation ℤ a f
  let z' : Fin t → Fin 2 → ℤ := fun i => z i - a
  let R := ((f.totalDegree : ℝ) + 1) * B
  have hdeg : q.totalDegree = f.totalDegree := affineTranslation_totalDegree a f
  have hprimq : PrimitiveIntegerPolynomial q := hprim.translate_affine a
  have hirq : Irreducible (MvPolynomial.map (Int.castRingHom F) q) := by
    dsimp [q]
    rw [affineTranslation_map, affineTranslation_irreducible_iff]
    exact hir
  have hinj' : Function.Injective z' := by
    intro i j hij
    apply hinj
    have hh := congrArg (fun v : Fin 2 → ℤ => v + a) hij
    simpa only [z', sub_add_cancel] using hh
  have hz' : ∀ i, eval (z' i) q = 0 := by
    intro i
    dsimp [q, z']
    rw [affineTranslation_eval, sub_add_cancel]
    exact hz i
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le
    (by have := Nat.cast_nonneg (α := ℝ) f.totalDegree; linarith) hB
  have hbox' : ∀ i j, |(z' i j : ℝ)| ≤ R := by
    intro i j
    exact homogeneousTranslation_integer_point_box hB a (z i) ha (hbox i) j
  have hcount' : ∀ ℓ : ℕ, ℓ.Prime → 27 * (q.totalDegree : ℝ) ^ 4 < (ℓ : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) q) →
      (Nat.card (PlaneResidue q ℓ) : ℝ) ≤ ℓ + C * (q.totalDegree : ℝ) ^ 2 * Real.sqrt ℓ := by
    intro ℓ hℓ hsize hirℓ
    rw [hdeg] at hsize ⊢
    have hirf : Irreducible (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) f) := by
      dsimp [q] at hirℓ
      rwa [affineTranslation_map, affineTranslation_irreducible_iff] at hirℓ
    rw [show Nat.card (PlaneResidue q ℓ) = Nat.card (PlaneResidue f ℓ) from
      affineTranslation_residue_card a f ℓ]
    exact hcount ℓ hℓ hsize hirf
  have hh := plane_finite_count_nonzero_constant q hprimq hirq (by rwa [hdeg]) ha0 z' hinj' hz'
    hR hbox' hC hcount'
  rw [hdeg] at hh
  have ht := hh.trans (mul_le_mul_of_nonneg_left (curveBound_translation_radius hd hB)
    (affineNonzeroConstantBound_pos C).le)
  convert ht using 1
  ring

/-- The same coefficient-uniform bound on the actual real-radius integer-point
counting interface. The only counting input is the sharp residue estimate. -/
theorem count_plane_of_sharp_residue_bound
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) (hd : 0 < f.totalDegree)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hcount : ∀ ℓ : ℕ, ℓ.Prime → 27 * (f.totalDegree : ℝ) ^ 4 < (ℓ : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) f) →
      (Nat.card (PlaneResidue f ℓ) : ℝ) ≤ ℓ + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt ℓ) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      (2 * Real.exp 1 * affineNonzeroConstantBound C) * curveBound f.totalDegree B := by
  apply integer_zero_count_le_of_family_bound
  intro t z hinj hz hbox
  exact plane_finite_count_of_sharp_residue_bound f hprim hir hd z hinj hz hB hbox hC hcount

end
end AffineCurveCounting
