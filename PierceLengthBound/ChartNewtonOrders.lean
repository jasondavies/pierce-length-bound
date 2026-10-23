/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ChartDiscreteOrders
public import PierceLengthBound.NewtonCoefficientDegrees

/-! The first Newton quartic on the projective chart: the chart gives the
coefficient-order bounds needed by `monic_quartic_quotient_discrete_order`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- If the first Newton quartic in the affine coordinates has order `-6e` at `-q`
for a valuation nonnegative on the chart with `ord((ι l)⁻¹) = e > 0`, then
`e = 2t` with `t > 0` and `ord(q) = -3t`. -/
theorem chart_newton_quotient_discrete_order {K F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K))
    (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (hl : ι l ≠ 0)
    (ν : AddValuation F (WithTop ℤ))
    (hregular : ∀ r : projectiveChart I ι l, 0 ≤ ν (r : F))
    {e : ℤ} (he : 0 < e) (hw : ν ((ι l)⁻¹) = (e : WithTop ℤ))
    (c : Fin 4 → K) (q : F)
    (hP : ν ((firstNewtonQuartic (fun j => algebraMap K F (c j))
      ![ι (Ideal.Quotient.mk I (X 0)), ι (Ideal.Quotient.mk I (X 1)),
        ι (Ideal.Quotient.mk I (X 2)), 0]).eval (-q)) = ((-6 * e : ℤ) : WithTop ℤ)) :
    ∃ t : ℤ, 0 < t ∧ e = 2 * t ∧ ν q = ((-3 * t : ℤ) : WithTop ℤ) := by
  let ψ := ι.comp (Ideal.Quotient.mkₐ K I)
  let s : Fin 4 → MvPolynomial (Fin 3) K := ![X 0, X 1, X 2, 0]
  let z : Fin 4 → F := ![ι (Ideal.Quotient.mk I (X 0)),
    ι (Ideal.Quotient.mk I (X 1)), ι (Ideal.Quotient.mk I (X 2)), 0]
  let p := firstNewtonCoeffs (fun j => algebraMap K F (c j)) z
  have hs (j : Fin 4) : (s j).totalDegree ≤ 1 := by fin_cases j <;> simp [s]
  have hmap (j : Fin 4) : ψ (firstNewtonCoeffs (fun j => C (c j)) s j) = p j := by
    change ψ.toRingHom (firstNewtonCoeffs _ _ j) = _
    rw [map_firstNewtonCoeffs]
    have hc (m : Fin 4) : ψ.toRingHom (C (c m)) = algebraMap K F (c m) := ψ.commutes _
    have hsj (m : Fin 4) : ψ.toRingHom (s m) = z m := by
      fin_cases m <;> simp [s, z, ψ]
    simp_rw [hc, hsj]
    rfl
  apply monic_quartic_quotient_discrete_order ν p q he
  · intro j
    have hh := chart_polynomial_discrete_order_ge I ι l hl ν hregular hw
      (firstNewtonCoeffs (fun j => C (c j)) s j) (4 - j.val)
      (firstNewtonCoeffs_totalDegree_sharp c s hs j)
    change (((-(4 - j.val : ℕ) : ℤ) * e : ℤ) : WithTop ℤ) ≤
      ν (ψ (firstNewtonCoeffs (fun j => C (c j)) s j)) at hh
    rw [hmap] at hh
    simpa only [Nat.cast_sub (show j.val ≤ 4 by omega), Nat.cast_ofNat] using hh
  · simpa only [firstNewtonQuartic_eval_neg] using hP

end
end PierceLengthBound.FixedDividend
