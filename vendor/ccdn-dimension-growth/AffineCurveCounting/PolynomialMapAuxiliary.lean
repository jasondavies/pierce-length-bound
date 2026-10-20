module

public import AffineCurveCounting.PolynomialMapDeterminant

/-! Auxiliary nonmultiples and explicit degree choices for polynomial images
of the original integer plane curve. Sharp finite-field counts remain explicit. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

theorem polynomial_map_exists_auxiliary_small_height
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) (hdM : d ≤ M)
    (q : MvPolynomial (Fin 2) ℤ) (hqdegree : q.totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) q))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |(q.coeff m : ℝ)| ≤ H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) q = 0)
    (himage : ∀ i, MvPolynomial.eval (fun j => MvPolynomial.eval (z i) (τ j)) f = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(MvPolynomial.eval (z i) (τ j) : ℝ)| ≤ B) (hC : 0 ≤ C)
    (hML : Real.log B ≤ M)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B)
    (hthreshold : 2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
      (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
        |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) < M)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) q) →
      (Nat.card (PlaneResidue q p) : ℝ) ≤
        p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
      (∀ i, MvPolynomial.eval (fun j => MvPolynomial.eval (z i) (τ j)) g = 0) ∧ ¬ f ∣ g := by
  classical
  by_contra hnone
  have hrel : ∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M →
      (∀ i, MvPolynomial.eval (fun j => MvPolynomial.eval (z i) (τ j)) g = 0) → f ∣ g := by
    intro g hg hv
    by_cases hg0 : g = 0
    · simp [hg0]
    · by_contra hnd
      exact hnone ⟨g, hg0, hg, hv, hnd⟩
  obtain ⟨s, _, _, hr, hc⟩ := polynomial_map_no_auxiliary_height_comparison
    order f hf hf0 hd hdM q hqdegree hir H hH hcoeff τ z hz himage hB hbox hC hrel hcount
  have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hlog := plane_auxiliary_log_degree_bound hd hdM hr hB hL hML hheight hc
  have hA : 0 < 1 + Real.log H / (d : ℝ) ^ 2 := by
    have := Real.log_nonneg hH
    positivity
  have hbound := plane_degree_bound_of_log_bound hd (lt_of_lt_of_le hd hdM)
    (by linarith) (by linarith) hA hlog
  exact (not_lt_of_ge hbound) hthreshold


theorem polynomial_map_exists_auxiliary_large_height
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) (hMlarge : 32 * d ≤ M)
    (q : MvPolynomial (Fin 2) ℤ) (hqdegree : q.totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) q))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |(q.coeff m : ℝ)| ≤ H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) q = 0)
    (himage : ∀ i, MvPolynomial.eval (fun j => MvPolynomial.eval (z i) (τ j)) f = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(MvPolynomial.eval (z i) (τ j) : ℝ)| ≤ B) (hC : 0 ≤ C)
    (T : ℝ) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2)
    (hthreshold : 8 * Real.exp (heightDeterminantError C + 6 + T) * (d : ℝ) ^ 3 < M)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) q) →
      (Nat.card (PlaneResidue q p) : ℝ) ≤
        p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
      (∀ i, MvPolynomial.eval (fun j => MvPolynomial.eval (z i) (τ j)) g = 0) ∧ ¬ f ∣ g := by
  classical
  have hdM : d ≤ M := by omega
  by_contra hnone
  have hrel : ∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M →
      (∀ i, MvPolynomial.eval (fun j => MvPolynomial.eval (z i) (τ j)) g = 0) → f ∣ g := by
    intro g hg hv
    by_cases hg0 : g = 0
    · simp [hg0]
    · by_contra hnd
      exact hnone ⟨g, hg0, hg, hv, hnd⟩
  obtain ⟨s, _, _, hr, hc⟩ := polynomial_map_no_auxiliary_height_comparison
    order f hf hf0 hd hdM q hqdegree hir H hH hcoeff τ z hz himage hB hbox hC hrel hcount
  have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hlog := plane_auxiliary_large_height_log_bound hd hMlarge hr hB hL hH hT
    hheight hposition hc
  have hbound := plane_large_degree_bound_of_log_bound hd (lt_of_lt_of_le hd hdM) hlog
  exact (not_lt_of_ge hbound) hthreshold


theorem polynomial_map_auxiliary_small_height_degree
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (q : MvPolynomial (Fin 2) ℤ) (hqdegree : q.totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) q))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |(q.coeff m : ℝ)| ≤ H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) q = 0)
    (himage : ∀ i, MvPolynomial.eval (fun j => MvPolynomial.eval (z i) (τ j)) f = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(MvPolynomial.eval (z i) (τ j) : ℝ)| ≤ B) (hC : 0 ≤ C)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) q) →
      (Nat.card (PlaneResidue q p) : ℝ) ≤
        p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    ∃ M : ℕ, (M : ℝ) ≤ d + Real.log B +
      2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
        (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
          |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) + 2 ∧
      ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, MvPolynomial.eval (fun j => MvPolynomial.eval (z i) (τ j)) g = 0) ∧ ¬ f ∣ g := by
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
  exact polynomial_map_exists_auxiliary_small_height order f hf hf0 hd hdM q hqdegree hir
    H hH hcoeff τ z hz himage hB hbox hC hML hheight hth hcount


theorem polynomial_map_auxiliary_large_height_degree
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (q : MvPolynomial (Fin 2) ℤ) (hqdegree : q.totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) q))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |(q.coeff m : ℝ)| ≤ H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) q = 0)
    (himage : ∀ i, MvPolynomial.eval (fun j => MvPolynomial.eval (z i) (τ j)) f = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(MvPolynomial.eval (z i) (τ j) : ℝ)| ≤ B) (hC : 0 ≤ C)
    (T : ℝ) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) q) →
      (Nat.card (PlaneResidue q p) : ℝ) ≤
        p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    ∃ M : ℕ, (M : ℝ) ≤ (34 + 8 * Real.exp (heightDeterminantError C + 6 + T)) * (d : ℝ) ^ 3 ∧
      ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, MvPolynomial.eval (fun j => MvPolynomial.eval (z i) (τ j)) g = 0) ∧ ¬ f ∣ g := by
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
  · exact polynomial_map_exists_auxiliary_large_height order f hf hf0 hd hMlarge q hqdegree hir
      H hH hcoeff τ z hz himage hB hbox hC T hT hheight hposition hth hcount


end
end AffineCurveCounting
