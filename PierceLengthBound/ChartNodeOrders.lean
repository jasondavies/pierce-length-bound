/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ChartNodeUnits

/-! Exact orders of all original node differences at valuations centered on
the actual nonexceptional infinity section. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

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
  have hunit := rational_nonexceptional_chart_node_difference_unit hρ hu hv hne
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

end
end PierceLengthBound.FixedDividend
