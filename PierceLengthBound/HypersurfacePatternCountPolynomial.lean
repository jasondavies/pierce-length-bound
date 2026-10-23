/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCountFiber

/-! # Polynomial families on a maximal-minor chart -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Matrix

/-- Variables on the chart are split into the last vertex `v` and the first vertex `(m,u)`. -/
abbrev HypersurfaceChartPolynomial := MvPolynomial (Fin 3 ⊕ Fin 4) ℚ

def chartFirstVertex (m : ℕ) (u : Fin 3 → ℤ) : Fin 4 → ℚ :=
  ![(m : ℚ), (u 0 : ℚ), (u 1 : ℚ), (u 2 : ℚ)]

/-- Regard a seven-variable chart polynomial as a ternary polynomial with four-variable
polynomial coefficients. -/
def chartPolynomialFamily (B : HypersurfaceChartPolynomial) :
    MvPolynomial (Fin 3) (MvPolynomial (Fin 4) ℚ) := sumAlgEquiv ℚ (Fin 3) (Fin 4) B

/-- Specialize the first vertex while leaving the final three coordinates indeterminate. -/
def chartPolynomialFiber (B : HypersurfaceChartPolynomial) (x : Fin 4 → ℚ) :
    MvPolynomial (Fin 3) ℚ := map (eval x) (chartPolynomialFamily B)

lemma chartPolynomialFiber_eval (B : HypersurfaceChartPolynomial)
    (x : Fin 4 → ℚ) (v : Fin 3 → ℚ) :
    eval v (chartPolynomialFiber B x) = eval (Sum.elim v x) B := by
  have hh : (eval v).comp ((map (eval x)).comp (sumAlgEquiv ℚ (Fin 3) (Fin 4)).toRingHom) =
      eval (Sum.elim v x) := by
    ext i
    · simp
    · cases i <;> simp
  exact DFunLike.congr_fun hh B

lemma chartPolynomialFiber_degree (B : HypersurfaceChartPolynomial) (x : Fin 4 → ℚ) :
    (chartPolynomialFiber B x).totalDegree ≤ (chartPolynomialFamily B).totalDegree := by
  classical
  unfold totalDegree
  exact Finset.sup_mono (support_map_subset _ _)

/-- A nonzero coefficient detects every identically-zero fiber. Its degree is fixed by the
chart polynomial and is independent of the specialized first vertex. -/
theorem chartPolynomialFiber_zero_certificate {B : HypersurfaceChartPolynomial} (hB : B ≠ 0) :
    ∃ q : MvPolynomial (Fin 4) ℚ, q ≠ 0 ∧
      ∀ x, chartPolynomialFiber B x = 0 → eval x q = 0 := by
  have hp : chartPolynomialFamily B ≠ 0 := by
    intro hz
    apply hB
    exact (sumAlgEquiv ℚ (Fin 3) (Fin 4)).injective (hz.trans (map_zero _).symm)
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hp
  refine ⟨(chartPolynomialFamily B).coeff d, hd, ?_⟩
  intro x hx
  have hc := congrArg (fun f : MvPolynomial (Fin 3) ℚ => f.coeff d) hx
  simpa [chartPolynomialFiber, coeff_map] using hc

/-- Scaling all variables by a nonzero rational is an invertible substitution. -/
lemma scalar_substitution_ne_zero {ι : Type*}
    {q : MvPolynomial ι ℚ} (hq : q ≠ 0) {g : ℚ} (hg : g ≠ 0) :
    aeval (fun i => C g * X i) q ≠ 0 := by
  let φ : MvPolynomial ι ℚ →ₐ[ℚ] MvPolynomial ι ℚ := aeval fun i => C g * X i
  let ψ : MvPolynomial ι ℚ →ₐ[ℚ] MvPolynomial ι ℚ := aeval fun i => C g⁻¹ * X i
  have he : ψ.comp φ = AlgHom.id ℚ (MvPolynomial ι ℚ) := by
    ext i : 1
    simp only [AlgHom.comp_apply, AlgHom.id_apply, φ, ψ, aeval_X, map_mul, aeval_C,
      MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hg, map_one, one_mul]
  intro hz
  have hc := DFunLike.congr_fun he q
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at hc
  rw [show φ q = 0 from hz, map_zero] at hc
  exact hq hc.symm

lemma scalar_substitution_degree {ι : Type*}
    (q : MvPolynomial ι ℚ) (g : ℚ) :
    (aeval (fun i => C g * X i) q).totalDegree ≤ q.totalDegree := by
  apply affine_hom_totalDegree_le
  intro i
  simp only [aeval_X]
  exact (totalDegree_mul _ _).trans (by simp)

lemma eval_scalar_substitution {ι : Type*}
    (q : MvPolynomial ι ℚ) (g : ℚ) (x : ι → ℚ) :
    eval x (aeval (fun i => C g * X i) q) = eval (fun i => g * x i) q := by
  have he : (aeval x).comp (aeval fun i => C g * X i) =
      aeval (fun i => g * x i) := by
    ext i
    simp
  exact DFunLike.congr_fun he q

end
end PierceLengthBound.FixedDividend
