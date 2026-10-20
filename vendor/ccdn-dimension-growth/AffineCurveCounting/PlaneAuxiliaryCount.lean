module

public import AffineCurveCounting.HomogeneousChart
public import AffineCurveCounting.PlaneAuxiliarySelection
public import AffineCurveCounting.Bezout

/-! Actual distinct-point bounds obtained from the auxiliary polynomials and
Bézout. The sharp finite-field estimate remains an explicit hypothesis. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma rational_map_totalDegree {σ : Type*} (f : MvPolynomial σ ℤ) :
    (MvPolynomial.map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree := by
  unfold totalDegree
  rw [support_map_of_injective _ Int.cast_injective]

lemma rational_irreducible_of_charZero_map {F σ : Type*} [Field F] [CharZero F]
    (f : MvPolynomial σ ℤ) (hf : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) :
    Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f) := by
  apply mvPolynomial_irreducible_of_field_map (algebraMap ℚ F)
  rw [map_map]
  have he : (algebraMap ℚ F).comp (Int.castRingHom ℚ) = Int.castRingHom F := by ext; simp
  rw [he]
  exact hf

/-- The precise Bézout step for an actual homogeneous integer auxiliary
polynomial and a primitive equation whose chart has full degree. -/
theorem plane_chart_points_card_le_auxiliary_degree {d M t : ℕ}
    (f g : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (hg : g.IsHomogeneous M) (hprim : PrimitiveIntegerPolynomial f)
    (hdchart : (planeAffineChart f).totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (planeAffineChart f)))
    (hnd : ¬ f ∣ g) (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hzf : ∀ i, eval (z i) (planeAffineChart f) = 0)
    (hzg : ∀ i, eval (Fin.cons 1 (z i)) g = 0) : t ≤ d * M := by
  let zQ : Fin t → Fin 2 → ℚ := fun i j => (z i j : ℚ)
  have hiQ : Function.Injective zQ := by
    intro i j he
    apply hinj
    funext k
    exact Int.cast_injective (congrFun he k)
  have hfQ : ∀ i, eval (zQ i) (MvPolynomial.map (Int.castRingHom ℚ) (planeAffineChart f)) = 0 := by
    intro i
    have h := congrArg (Int.castRingHom ℚ) (hzf i)
    rw [map_eval, map_zero] at h
    exact h
  have hgQ : ∀ i, eval (zQ i) (MvPolynomial.map (Int.castRingHom ℚ) (planeAffineChart g)) = 0 := by
    intro i
    have h := congrArg (Int.castRingHom ℚ) (hzg i)
    rw [← planeAffineChart_eval] at h
    rw [map_eval, map_zero] at h
    exact h
  have hndQ : ¬ MvPolynomial.map (Int.castRingHom ℚ) (planeAffineChart f) ∣
      MvPolynomial.map (Int.castRingHom ℚ) (planeAffineChart g) :=
    rational_affineChart_not_dvd hf hf0 hg hprim hdchart hnd
  have h := plane_common_zeros_card_le _ _ hir hndQ zQ hiQ hfQ hgQ
  rw [Fintype.card_fin, rational_map_totalDegree, rational_map_totalDegree, hdchart] at h
  exact h.trans (Nat.mul_le_mul_left d ((affineChart_totalDegree_le g).trans hg.totalDegree_le))

/-- In the small-height range, the explicit selected auxiliary degree yields
a point count. All geometric data here are actual equations and integer points. -/
theorem plane_chart_points_small_height_bound
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (hprim : PrimitiveIntegerPolynomial f)
    (hdchart : (planeAffineChart f).totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) (planeAffineChart f)))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |((planeAffineChart f).coeff m : ℝ)| ≤ H)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hz : ∀ i, eval (z i) (planeAffineChart f) = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) (planeAffineChart f)) →
      (Nat.card (PlaneResidue (planeAffineChart f) p) : ℝ) ≤
        p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    (t : ℝ) ≤ d * (d + Real.log B +
      2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
        (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
          |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) + 2) := by
  obtain ⟨M, hM, g, _, hg, hzg, hnd⟩ := plane_chart_auxiliary_small_height_degree
    order f hf hf0 hd hdchart hir H hH hcoeff z hz hB hbox hC hheight hcount
  have h := plane_chart_points_card_le_auxiliary_degree f g hf hf0 hg hprim hdchart
    (rational_irreducible_of_charZero_map _ hir) hnd z hinj hz hzg
  have hR : (t : ℝ) ≤ d * (M : ℝ) := by exact_mod_cast h
  exact hR.trans (mul_le_mul_of_nonneg_left hM (by positivity))

/-- The large-height range gives a uniform O(d⁴) distinct-point bound, with
explicit finite-field and leading-position hypotheses. -/
theorem plane_chart_points_large_height_bound
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (hprim : PrimitiveIntegerPolynomial f)
    (hdchart : (planeAffineChart f).totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) (planeAffineChart f)))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |((planeAffineChart f).coeff m : ℝ)| ≤ H)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hz : ∀ i, eval (z i) (planeAffineChart f) = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (T : ℝ) (hT : 0 ≤ T) (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) (planeAffineChart f)) →
      (Nat.card (PlaneResidue (planeAffineChart f) p) : ℝ) ≤
        p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    (t : ℝ) ≤ (34 + 8 * Real.exp (heightDeterminantError C + 6 + T)) * (d : ℝ) ^ 4 := by
  obtain ⟨M, hM, g, _, hg, hzg, hnd⟩ := plane_chart_auxiliary_large_height_degree
    order f hf hf0 hd hdchart hir H hH hcoeff z hz hB hbox hC T hT hheight hposition hcount
  have h := plane_chart_points_card_le_auxiliary_degree f g hf hf0 hg hprim hdchart
    (rational_irreducible_of_charZero_map _ hir) hnd z hinj hz hzg
  have hR : (t : ℝ) ≤ d * (M : ℝ) := by exact_mod_cast h
  calc
    _ ≤ d * ((34 + 8 * Real.exp (heightDeterminantError C + 6 + T)) * (d : ℝ) ^ 3) :=
      hR.trans (mul_le_mul_of_nonneg_left hM (by positivity))
    _ = _ := by ring

/-- Enumerating the actual integer zeros transfers finite-family bounds to
the counting interface, including empty point sets. -/
lemma integer_zero_count_le_of_family_bound {n : ℕ} (f : MvPolynomial (Fin n) ℤ)
    (B R : ℝ)
    (hbound : ∀ (t : ℕ) (z : Fin t → Fin n → ℤ), Function.Injective z →
      (∀ i, eval (z i) f = 0) → (∀ i j, |(z i j : ℝ)| ≤ B) → (t : ℝ) ≤ R) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) f)) B : ℝ) ≤ R := by
  classical
  let S := integralPoints (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) f)) B
  let e := (Fintype.equivFin S).symm
  let z : Fin (Fintype.card S) → Fin n → ℤ := fun i => (e i).val
  have hinj : Function.Injective z := Subtype.val_injective.comp e.injective
  have hzero : ∀ i, eval (z i) f = 0 := by
    intro i
    apply Int.cast_injective (α := ℚ)
    have h := (mem_integralPoints.mp (e i).property).2
    change eval (fun j => (z i j : ℚ)) (MvPolynomial.map (Int.castRingHom ℚ) f) = 0 at h
    change (Int.castRingHom ℚ) (eval (z i) f) = 0
    rw [map_eval]
    exact h
  have hbox : ∀ i j, |(z i j : ℝ)| ≤ B := fun i => (mem_integralPoints.mp (e i).property).1
  have h := hbound _ z hinj hzero hbox
  simpa only [Fintype.card_coe, S, count] using h

/-- The finite-family bound in the actual real-radius counting interface. -/
theorem count_plane_chart_small_height_bound
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (hprim : PrimitiveIntegerPolynomial f)
    (hdchart : (planeAffineChart f).totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) (planeAffineChart f)))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |((planeAffineChart f).coeff m : ℝ)| ≤ H)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) (planeAffineChart f)) →
      (Nat.card (PlaneResidue (planeAffineChart f) p) : ℝ) ≤
        p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) (planeAffineChart f))) B : ℝ) ≤ d * (d + Real.log B +
      2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
        (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
          |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) + 2) := by
  apply integer_zero_count_le_of_family_bound
  intro t z hinj hz hbox
  exact plane_chart_points_small_height_bound order f hf hf0 hd hprim hdchart hir H hH hcoeff z hinj hz hB hbox hC hheight hcount

/-- The finite-family bound in the actual real-radius counting interface. -/
theorem count_plane_chart_large_height_bound
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (hprim : PrimitiveIntegerPolynomial f)
    (hdchart : (planeAffineChart f).totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) (planeAffineChart f)))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |((planeAffineChart f).coeff m : ℝ)| ≤ H)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (T : ℝ) (hT : 0 ≤ T) (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) (planeAffineChart f)) →
      (Nat.card (PlaneResidue (planeAffineChart f) p) : ℝ) ≤
        p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) (planeAffineChart f))) B : ℝ) ≤ (34 + 8 * Real.exp (heightDeterminantError C + 6 + T)) * (d : ℝ) ^ 4 := by
  apply integer_zero_count_le_of_family_bound
  intro t z hinj hz hbox
  exact plane_chart_points_large_height_bound order f hf hf0 hd hprim hdchart hir H hH hcoeff z hinj hz hB hbox hC T hT hheight hposition hcount

end
end AffineCurveCounting
