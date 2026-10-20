module

public import AffineCurveCounting.ScaledPlaneCount

/-! The unit-scaled model gives a coefficient-uniform 2/d fallback and a
large-coefficient O(d^4) count, without requiring a scaling prime. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Real

lemma PrimitiveIntegerPolynomial.scaledHomogenize_one {n : ℕ}
    {f : MvPolynomial (Fin n) ℤ} (hf : PrimitiveIntegerPolynomial f) (d : ℕ) :
    PrimitiveIntegerPolynomial (AffineCurveCounting.scaledHomogenize d 1 f) := by
  intro c hc
  apply hf c
  intro m
  have h := hc (homogenizedExponent d m)
  simpa only [scaledHomogenize_coefficient, one_pow, one_mul] using h

lemma unscaled_positioned_points_card_le {M t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f))
    (a : Fin 2 → ℤ) (g : MvPolynomial (Fin 3) ℤ) (hg : g.IsHomogeneous M)
    (hnd : ¬ homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree 1 f) ∣ g)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hz : ∀ i, eval (z i) f = 0)
    (hzg : ∀ i, eval (fun j => eval (z i) (scaledModelCoordinates 1 a j)) g = 0) :
    t ≤ f.totalDegree * M := by
  obtain ⟨g', hg', he, hnd'⟩ := scaledModelCoordinates_auxiliary_transport 1 a f g hg hnd
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
  have hchart : planeAffineChart (scaledHomogenize f.totalDegree 1 f) = f := by
    change homogeneousSlice 2 1 (scaledHomogenize f.totalDegree 1 f) = f
    simp only [homogeneousSlice_scaledHomogenize 1 f le_rfl, one_pow, map_one, one_mul]
  have hh := plane_chart_points_card_le_auxiliary_degree (scaledHomogenize f.totalDegree 1 f) g'
    (scaledHomogenize_homogeneous _ _ le_rfl) (scaledHomogenize_ne_zero _ one_ne_zero hf0)
    hg' (hprim.scaledHomogenize_one _) (by rw [hchart]) (by rwa [hchart]) hnd' z hinj
    (by simpa only [hchart] using hz) (fun i => (he (z i)).trans (hzg i))
  exact hh

/-- Coefficient positioning removes the coefficient height from the 2/d
fallback bound. This holds for any primitive absolutely irreducible equation. -/
theorem unscaled_plane_finite_count
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) (hd : 0 < f.totalDegree)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z) (hz : ∀ i, eval (z i) f = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (hcount : ∀ ℓ : ℕ, ℓ.Prime → 27 * (f.totalDegree : ℝ) ^ 4 < (ℓ : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) f) →
      (Nat.card (PlaneResidue f ℓ) : ℝ) ≤ ℓ + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt ℓ) :
    (t : ℝ) ≤ max
      ((f.totalDegree : ℝ) * scaledPlaneAuxiliaryDegreeBound f.totalDegree C
        (((f.totalDegree : ℝ) + 1) * B) 1)
      ((34 + 8 * Real.exp (heightDeterminantError C + 20)) * (f.totalDegree : ℝ) ^ 4) := by
  let d := f.totalDegree
  let R := ((d : ℝ) + 1) * B
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le (by linarith) hB
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
  obtain ⟨a, H, ha, hH, _, hc, hlo, hhi⟩ := exists_scaled_model_position f hf0 hd (h := 1) le_rfl
  let model := homogeneousTranslation ℤ a (scaledHomogenize d 1 f)
  have hmhom : model.IsHomogeneous d :=
    homogeneousTranslation_homogeneous a (scaledHomogenize_homogeneous _ _ le_rfl)
  have hm0 : model ≠ 0 := by
    have he := (homogeneousTranslation ℤ a).injective.ne (scaledHomogenize_ne_zero d one_ne_zero hf0)
    simpa only [map_zero] using he
  let τ := scaledModelCoordinates 1 a
  have hmodel : ∀ i, eval (fun j => eval (z i) (τ j)) model = 0 := by
    intro i
    change eval (fun j => eval (z i) (scaledModelCoordinates 1 a j))
      (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree 1 f)) = 0
    rw [scaledModelCoordinates_model_eval, hz i, mul_zero]
  have himagebox : ∀ i j, |(eval (z i) (τ j) : ℝ)| ≤ R := by
    intro i j
    exact scaledModelCoordinates_box hB (by norm_num) (by simpa using hB) a (z i) ha (hbox i) j
  have hirq := rational_irreducible_of_charZero_map f hir
  by_cases hsmall : Real.log H ≤ 4 * d * Real.log R
  · obtain ⟨M, hM, g, _, hg, hzg, hnd⟩ := polynomial_map_auxiliary_small_height_degree
      MonomialOrder.lex model hmhom hm0 hd f rfl hir H hH hc τ z hz hmodel hR himagebox hC
      (hlo.trans hsmall) hcount
    have ht := unscaled_positioned_points_card_le f hprim hirq a g hg hnd z hinj hz hzg
    have htR : (t : ℝ) ≤ d * (M : ℝ) := by exact_mod_cast ht
    have hL : 0 < |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (MonomialOrder.lex.leadingCoeff_ne_zero_iff.mpr hm0))
    have hratio := scaled_positioned_height_ratio_le hd (h := 1) le_rfl (by simpa using hH) hL hhi
    simp only [Real.log_one, zero_div, add_zero, Real.one_rpow, div_one] at hratio
    have ht := mul_le_mul_of_nonneg_left hratio (show 0 ≤
      2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 * R ^ (2 / (d : ℝ)) by positivity)
    have hterm : 2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
        (1 + Real.log H / (d : ℝ) ^ 2) * R ^ (2 / (d : ℝ)) /
          |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) ≤
        2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * (d : ℝ) ^ 3 * R ^ (2 / (d : ℝ)) := by
      convert ht using 1 <;> ring
    have hMb : (M : ℝ) ≤ scaledPlaneAuxiliaryDegreeBound d C R 1 := by
      unfold scaledPlaneAuxiliaryDegreeBound
      simp only [Real.log_one, zero_div, add_zero, mul_one, Real.one_rpow, div_one]
      linarith
    exact (htR.trans (mul_le_mul_of_nonneg_left hMb hdR.le)).trans (le_max_left _ _)
  · obtain ⟨M, hM, g, _, hg, hzg, hnd⟩ := polynomial_map_auxiliary_large_height_degree
      MonomialOrder.lex model hmhom hm0 hd f rfl hir H hH hc τ z hz hmodel hR himagebox hC
      14 (by norm_num) (le_of_lt (lt_of_not_ge hsmall)) hhi hcount
    have ht := unscaled_positioned_points_card_le f hprim hirq a g hg hnd z hinj hz hzg
    have htR : (t : ℝ) ≤ d * (M : ℝ) := by exact_mod_cast ht
    apply (htR.trans (mul_le_mul_of_nonneg_left hM hdR.le)).trans
    calc
      _ = (34 + 8 * Real.exp (heightDeterminantError C + 20)) * (d : ℝ) ^ 4 := by
        rw [show heightDeterminantError C + 6 + 14 = heightDeterminantError C + 20 by ring]
        ring
      _ ≤ _ := le_max_right _ _

/-- A sufficiently large actual coefficient forces the large-height branch
and gives O(d^4), without any prime-selection assumption. -/
theorem unscaled_plane_finite_count_large_coefficient
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) (hd : 0 < f.totalDegree)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z) (hz : ∀ i, eval (z i) f = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (m : Fin 2 →₀ ℕ) (hm : f.coeff m ≠ 0)
    (hheight : 4 * (f.totalDegree : ℝ) * Real.log (((f.totalDegree : ℝ) + 1) * B) ≤
      Real.log |(f.coeff m : ℝ)|)
    (hcount : ∀ ℓ : ℕ, ℓ.Prime → 27 * (f.totalDegree : ℝ) ^ 4 < (ℓ : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) f) →
      (Nat.card (PlaneResidue f ℓ) : ℝ) ≤ ℓ + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt ℓ) :
    (t : ℝ) ≤ (34 + 8 * Real.exp (heightDeterminantError C + 20)) * (f.totalDegree : ℝ) ^ 4 := by
  let d := f.totalDegree
  let R := ((d : ℝ) + 1) * B
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le (by linarith) hB
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
  obtain ⟨a, H, ha, hH, _, hc, _, hhi⟩ := exists_scaled_model_position f hf0 hd (h := 1) le_rfl
  let model := homogeneousTranslation ℤ a (scaledHomogenize d 1 f)
  have hmhom : model.IsHomogeneous d :=
    homogeneousTranslation_homogeneous a (scaledHomogenize_homogeneous _ _ le_rfl)
  have hm0 : model ≠ 0 := by
    have he := (homogeneousTranslation ℤ a).injective.ne (scaledHomogenize_ne_zero d one_ne_zero hf0)
    simpa only [map_zero] using he
  let τ := scaledModelCoordinates 1 a
  have hmodel : ∀ i, eval (fun j => eval (z i) (τ j)) model = 0 := by
    intro i
    change eval (fun j => eval (z i) (scaledModelCoordinates 1 a j))
      (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree 1 f)) = 0
    rw [scaledModelCoordinates_model_eval, hz i, mul_zero]
  have himagebox : ∀ i j, |(eval (z i) (τ j) : ℝ)| ≤ R := by
    intro i j
    exact scaledModelCoordinates_box hB (by norm_num) (by simpa using hB) a (z i) ha (hbox i) j
  have hirq := rational_irreducible_of_charZero_map f hir
  have hlarge : 4 * d * Real.log R ≤ Real.log H := hheight.trans
    (Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hm)) (hc m))
  obtain ⟨M, hM, g, _, hg, hzg, hnd⟩ := polynomial_map_auxiliary_large_height_degree
    MonomialOrder.lex model hmhom hm0 hd f rfl hir H hH hc τ z hz hmodel hR himagebox hC
    14 (by norm_num) hlarge hhi hcount
  have ht := unscaled_positioned_points_card_le f hprim hirq a g hg hnd z hinj hz hzg
  have htR : (t : ℝ) ≤ d * (M : ℝ) := by exact_mod_cast ht
  have ht' := htR.trans (mul_le_mul_of_nonneg_left hM hdR.le)
  rw [show heightDeterminantError C + 6 + 14 = heightDeterminantError C + 20 by ring] at ht'
  convert ht' using 1
  ring

end
end AffineCurveCounting
