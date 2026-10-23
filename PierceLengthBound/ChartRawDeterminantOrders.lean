/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ChartNodeUnits
public import PierceLengthBound.RawDeterminantTotalDegree
public import PierceLengthBound.ChartDiscreteOrders
public import PierceLengthBound.IntegralLiftQuotientNormalization

/-! Exact raw Hankel determinant orders on the actual nonexceptional chart.
The degree-six Vandermonde dominates its entire degree-at-most-five remainder. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial
noncomputable section

/-! Exact orders of all original node differences at valuations centered on
the actual nonexceptional infinity section. -/

lemma completeDirection_mul_right {R : Type*} [CommRing R]
    (ρ u v : R) (z : Fin 3 → R) (w : R) (j : Fin 5) :
    completeDirection ρ u v (fun k => z k * w) j = completeDirection ρ u v z j * w := by
  fin_cases j <;> simp only [Fin.reduceFinMk, completeDirection, fourthNode, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons, zero_mul]
  all_goals ring

/-- Every pair of distinct original nodes has exactly the original infinity
pole order, with no additional noncollision hypothesis on the valuation. -/
theorem nonexceptional_node_difference_discrete_order
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (ha : a ≠ 0) (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (ν : AddValuation F (WithTop ℤ))
    (hregular : ∀ r : projectiveChart I ι (Ideal.Quotient.mk I (X 0)), 0 ≤ ν (r : F))
    {e : ℤ} (he : 0 < e)
    (hw : ν ((ι (Ideal.Quotient.mk I (X 0)))⁻¹) = (e : WithTop ℤ))
    (j k : Fin 5) (hjk : j ≠ k) :
    let z := completeDirection (algebraMap ℚ F ρ) (algebraMap ℚ F u)
      (algebraMap ℚ F v) (fun m => ι (Ideal.Quotient.mk I (X m)))
    ν (z j - z k) = ((-e : ℤ) : WithTop ℤ) := by
  dsimp only
  let l := Ideal.Quotient.mk I (X 0)
  let R := projectiveChart I ι l
  let z := completeDirection (algebraMap ℚ R ρ) (algebraMap ℚ R u)
    (algebraMap ℚ R v) (chartNode I ι l)
  have hunit := nonexceptional_chart_node_difference_unit hρ hu hv hne
    ρ' u' v' A a ha I hf hg ι hι hd hdegree j k hjk
  have hz := discrete_order_unit_mod_infinity ν R.subtype hregular
    (w := chartInfinityCoordinate I ι l) (r := z j - z k)
    (by change 0 < ν ((ι l)⁻¹); rw [hw]; exact_mod_cast he) hunit
  have hnode (m : Fin 5) : R.subtype (z m) =
      completeDirection (algebraMap ℚ F ρ) (algebraMap ℚ F u) (algebraMap ℚ F v)
        (fun n => ι (Ideal.Quotient.mk I (X n))) m * (ι l)⁻¹ := by
    dsimp only [z]
    have hm := map_completeDirection R.subtype (algebraMap ℚ R ρ)
      (algebraMap ℚ R u) (algebraMap ℚ R v) (chartNode I ι l) m
    refine hm.trans ?_
    change completeDirection (algebraMap ℚ F ρ) (algebraMap ℚ F u)
      (algebraMap ℚ F v) (fun n => (chartNode I ι l n : F)) m = _
    simp_rw [chartNode_val]
    exact completeDirection_mul_right _ _ _ _ _ _
  rw [map_sub, hnode, hnode, ← sub_mul, ν.map_mul, hw] at hz
  let y := completeDirection (algebraMap ℚ F ρ) (algebraMap ℚ F u)
    (algebraMap ℚ F v) (fun n => ι (Ideal.Quotient.mk I (X n)))
  have htop : ν (y j - y k) ≠ ⊤ := by
    intro ht
    change ν (y j - y k) + (e : WithTop ℤ) = 0 at hz
    rw [ht, top_add] at hz
    exact WithTop.top_ne_coe hz
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
  change ν (y j - y k) + (e : WithTop ℤ) = 0 at hz
  change ν (y j - y k) = _
  rw [← hr] at hz ⊢
  have hr' : r + e = 0 := by exact_mod_cast hz
  congr 1
  omega

/-- Both consecutive raw cubic determinants have order -3e and the fourth
determinant has order -6e at every centered discrete
valuation of an actual nonexceptional component. Their leading nonvanishing
and the lower-term bounds are derived from the chart, not supplied as premises. -/
theorem nonexceptional_raw_determinant_discrete_orders
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (ha : a ≠ 0) (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (ν : AddValuation F (WithTop ℤ))
    (hregular : ∀ r : projectiveChart I ι (Ideal.Quotient.mk I (X 0)), 0 ≤ ν (r : F))
    {e : ℤ} (he : 0 < e)
    (hw : ν ((ι (Ideal.Quotient.mk I (X 0)))⁻¹) = (e : WithTop ℤ)) :
    let x := fun j => ι (Ideal.Quotient.mk I (X j))
    let k := lineGaps (algebraMap ℚ F ρ) (algebraMap ℚ F u) (algebraMap ℚ F v)
      (algebraMap ℚ F ρ') (algebraMap ℚ F u') (algebraMap ℚ F v') (x 0) (x 1) (x 2)
    ν (rawHankelThree (k 0) (k 1) (k 2)) = ((-3 * e : ℤ) : WithTop ℤ) ∧
      ν (rawHankelThree (k 1) (k 2) (k 3)) = ((-3 * e : ℤ) : WithTop ℤ) ∧
      ν (muH4 (k 0) (k 1) (k 2) (k 3) (k 4)) = ((-6 * e : ℤ) : WithTop ℤ) := by
  dsimp only
  let x := fun j => ι (Ideal.Quotient.mk I (X j))
  let k := lineGaps (algebraMap ℚ F ρ) (algebraMap ℚ F u) (algebraMap ℚ F v)
    (algebraMap ℚ F ρ') (algebraMap ℚ F u') (algebraMap ℚ F v') (x 0) (x 1) (x 2)
  let z := completeDirection (algebraMap ℚ F ρ) (algebraMap ℚ F u)
    (algebraMap ℚ F v) x
  have hord (j m : Fin 5) (hjm : j ≠ m) : ν (z j - z m) = ((-e : ℤ) : WithTop ℤ) :=
    nonexceptional_node_difference_discrete_order hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree ν hregular he hw j m hjm
  have h0 : ν (k 0) = ((-e : ℤ) : WithTop ℤ) := by
    simpa [k, z, lineGaps, completeDirection] using hord 1 0 (by decide)
  have h1 : ν (k 1) = ((-e : ℤ) : WithTop ℤ) := by
    simpa [k, z, lineGaps, completeDirection] using hord 2 1 (by decide)
  have h2 : ν (k 2) = ((-e : ℤ) : WithTop ℤ) := by
    simpa [k, z, lineGaps, completeDirection] using hord 3 2 (by decide)
  have h3 : ν (k 3) = ((-e : ℤ) : WithTop ℤ) := by
    simpa [k, z, lineGaps, completeDirection] using hord 4 3 (by decide)
  have h01 : ν (k 0 + k 1) = ((-e : ℤ) : WithTop ℤ) := by
    simpa [k, z, lineGaps, completeDirection] using hord 2 0 (by decide)
  have h12 : ν (k 1 + k 2) = ((-e : ℤ) : WithTop ℤ) := by
    have hh : k 1 + k 2 = z 3 - z 1 := by simp [k, z, lineGaps, completeDirection]
    rw [hh]
    exact hord 3 1 (by decide)
  have h012 : ν (k 0 + k 1 + k 2) = ((-e : ℤ) : WithTop ℤ) := by
    simpa [k, z, lineGaps, completeDirection] using hord 3 0 (by decide)
  refine ⟨rawHankelThree_discrete_order ν he h0 h1 h01 h2.ge,
    rawHankelThree_discrete_order ν he h1 h2 h12 h3.ge, ?_⟩
  let kp : Fin 5 → MvPolynomial (Fin 3) ℚ :=
    lineGaps (C ρ) (C u) (C v) (C ρ') (C u') (C v') (X 0) (X 1) (X 2)
  let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
  have hψ (j : Fin 5) : ψ (kp j) = k j := by
    change ψ.toRingHom (lineGaps _ _ _ _ _ _ _ _ _ j) = _
    rw [map_lineGaps]
    have hc (c : ℚ) : ψ.toRingHom (C c) = algebraMap ℚ F c := ψ.commutes c
    rw [hc, hc, hc, hc, hc, hc]
    rfl
  have hl : ι (Ideal.Quotient.mk I (X 0)) ≠ 0 := by
    intro hz
    rw [hz, inv_zero, ν.map_zero] at hw
    exact WithTop.top_ne_coe hw
  have hlow : ((-5 * e : ℤ) : WithTop ℤ) ≤ ν (rawDetLower (k 0) (k 1) (k 2) (k 3) (k 4)) := by
    have hh := chart_polynomial_discrete_order_ge I ι _ hl ν hregular hw
      (rawDetLower (kp 0) (kp 1) (kp 2) (kp 3) (kp 4)) 5
      (rawDetLower_totalDegree kp (lineGaps_totalDegree ρ u v ρ' u' v'))
    change ((-5 * e : ℤ) : WithTop ℤ) ≤
      ν (ψ.toRingHom (rawDetLower (kp 0) (kp 1) (kp 2) (kp 3) (kp 4))) at hh
    rw [map_rawDetLower] at hh
    change ((-5 * e : ℤ) : WithTop ℤ) ≤
      ν (rawDetLower (ψ (kp 0)) (ψ (kp 1)) (ψ (kp 2)) (ψ (kp 3)) (ψ (kp 4))) at hh
    simpa only [hψ] using hh
  have hlead : ν (k 0 * k 1 * k 2 * (k 0 + k 1) * (k 1 + k 2) *
      (k 0 + k 1 + k 2)) = ((-6 * e : ℤ) : WithTop ℤ) := by
    simp only [ν.map_mul, h0, h1, h2, h01, h12, h012]
    norm_cast
    omega
  change ν (muH4 (k 0) (k 1) (k 2) (k 3) (k 4)) = _
  rw [muH4_leading_decomposition, ν.map_add_eq_of_lt_left, hlead]
  rw [hlead]
  exact lt_of_lt_of_le (by exact_mod_cast (show -6 * e < -5 * e by omega)) hlow

end
end PierceLengthBound.FixedDividend
