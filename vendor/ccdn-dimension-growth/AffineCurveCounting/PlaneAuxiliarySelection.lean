module

public import AffineCurveCounting.PlaneAuxiliaryLargeHeight

/-! Explicit integer degree choices for both coefficient-height ranges. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

lemma auxiliary_integer_degree_selection (d : ℕ) {l R : ℝ} (hl : 0 ≤ l) (hR : 0 ≤ R) :
    ∃ M : ℕ, d ≤ M ∧ l ≤ M ∧ R < M ∧ (M : ℝ) ≤ d + l + R + 2 := by
  refine ⟨d + ⌈l⌉₊ + ⌊R⌋₊ + 1, by omega, ?_, ?_, ?_⟩
  · have h := Nat.le_ceil l
    push_cast
    linarith [show (0 : ℝ) ≤ d by positivity, show (0 : ℝ) ≤ ⌊R⌋₊ by positivity]
  · have h := Nat.lt_floor_add_one R
    push_cast
    linarith [show (0 : ℝ) ≤ d by positivity, show (0 : ℝ) ≤ ⌈l⌉₊ by positivity]
  · have hc := Nat.ceil_lt_add_one hl
    have hf := Nat.floor_le hR
    push_cast
    linarith

/-- In the small-height range, choose the auxiliary degree explicitly. -/
theorem plane_chart_auxiliary_small_height_degree
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (hdchart : (planeAffineChart f).totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) (planeAffineChart f)))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |((planeAffineChart f).coeff m : ℝ)| ≤ H)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) (planeAffineChart f) = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) (planeAffineChart f)) →
      (Nat.card (PlaneResidue (planeAffineChart f) p) : ℝ) ≤
        p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    ∃ M : ℕ, (M : ℝ) ≤ d + Real.log B +
      2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
        (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
          |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) + 2 ∧
      ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, MvPolynomial.eval (Fin.cons 1 (z i)) g = 0) ∧ ¬ f ∣ g := by
  let R := 2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
    (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
      |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2)
  have hR : 0 ≤ R := by
    have := Real.log_nonneg hH
    have hB0 : 0 ≤ B := by linarith
    dsimp only [R]
    positivity
  obtain ⟨M, hdM, hML, hth, hM⟩ := auxiliary_integer_degree_selection d (Real.log_nonneg hB) hR
  refine ⟨M, hM, ?_⟩
  exact plane_chart_exists_auxiliary_small_height order f hf hf0 hd hdM hdchart hir
    H hH hcoeff z hz hB hbox hC hML hheight hth hcount

/-- In the large-height range the chosen degree is bounded uniformly by a
constant times d³, retaining explicit arithmetic and coordinate hypotheses. -/
theorem plane_chart_auxiliary_large_height_degree
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (hdchart : (planeAffineChart f).totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) (planeAffineChart f)))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |((planeAffineChart f).coeff m : ℝ)| ≤ H)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) (planeAffineChart f) = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (T : ℝ) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) (planeAffineChart f)) →
      (Nat.card (PlaneResidue (planeAffineChart f) p) : ℝ) ≤
        p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    ∃ M : ℕ, (M : ℝ) ≤ (34 + 8 * Real.exp (heightDeterminantError C + 6 + T)) * (d : ℝ) ^ 3 ∧
      ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, MvPolynomial.eval (Fin.cons 1 (z i)) g = 0) ∧ ¬ f ∣ g := by
  let R := 8 * Real.exp (heightDeterminantError C + 6 + T) * (d : ℝ) ^ 3
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  obtain ⟨M, hMlarge, _, hth, hM⟩ := auxiliary_integer_degree_selection (32 * d)
    (show (0 : ℝ) ≤ 0 from le_rfl) hR
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hd31 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := le_trans hd1 hd3
  refine ⟨M, ?_, ?_⟩
  · dsimp only [R] at hM
    push_cast at hM
    nlinarith
  · exact plane_chart_exists_auxiliary_large_height order f hf hf0 hd hMlarge hdchart hir
      H hH hcoeff z hz hB hbox hC T hT hheight hposition hth hcount

end
end AffineCurveCounting
