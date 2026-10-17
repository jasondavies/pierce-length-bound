import Mathlib

/-!
# Hadamard's inequality

For a positive definite real matrix `G`, `det G ≤ ∏ᵢ Gᵢᵢ`. Rescale by `D = diag(Gᵢᵢ^{-1/2})`:
`M = D G D` is positive semidefinite with unit diagonal, so its eigenvalues `λᵢ ≥ 0` have
`∑ λᵢ = tr M = n`, and `∏ λᵢ ≤ ∏ exp(λᵢ - 1) = exp(∑ λᵢ - n) = 1`.
-/

namespace PierceBound

open Matrix Finset

/-- **Hadamard's inequality.** -/
theorem det_le_prod_diag {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) :
    G.det ≤ ∏ i, G i i := by
  have hd : ∀ i, 0 < G i i := fun i => hG.diag_pos
  set D : Matrix (Fin n) (Fin n) ℝ := diagonal fun i => (Real.sqrt (G i i))⁻¹ with hD
  have hDt : Dᴴ = D := by
    simp [D]
  have hM : (Dᴴ * G * D).PosSemidef := hG.posSemidef.conjTranspose_mul_mul_same D
  rw [hDt] at hM
  set M := D * G * D with hMdef
  have hsq : ∀ i, (Real.sqrt (G i i))⁻¹ * (Real.sqrt (G i i))⁻¹ = (G i i)⁻¹ := by
    intro i
    rw [← mul_inv, Real.mul_self_sqrt (hd i).le]
  have hMii : ∀ i, M i i = 1 := by
    intro i
    simp only [M, D, mul_diagonal, diagonal_mul]
    rw [show (Real.sqrt (G i i))⁻¹ * G i i * (Real.sqrt (G i i))⁻¹ =
      ((Real.sqrt (G i i))⁻¹ * (Real.sqrt (G i i))⁻¹) * G i i by ring, hsq i,
      inv_mul_cancel₀ (hd i).ne']
  have hdetM : M.det = G.det * ∏ i, (G i i)⁻¹ := by
    simp only [M, det_mul, D, det_diagonal]
    rw [mul_comm ((∏ i, (Real.sqrt (G i i))⁻¹)) G.det, mul_assoc, ← prod_mul_distrib]
    simp only [hsq]
  have htr : M.trace = n := by
    simp [trace, hMii]
  -- eigenvalues
  have hH := hM.isHermitian
  have hev : ∀ i, 0 ≤ hH.eigenvalues i := hM.eigenvalues_nonneg
  have hdet : M.det = ∏ i, hH.eigenvalues i := by
    rw [hH.det_eq_prod_eigenvalues]; simp
  have htr' : ∑ i, hH.eigenvalues i = n := by
    rw [← htr, hH.trace_eq_sum_eigenvalues]; simp
  have hle : ∏ i, hH.eigenvalues i ≤ 1 := by
    calc ∏ i, hH.eigenvalues i ≤ ∏ i, Real.exp (hH.eigenvalues i - 1) :=
          Finset.prod_le_prod₀ (fun i _ => hev i) fun i _ => by
            have := Real.add_one_le_exp (hH.eigenvalues i - 1); linarith
      _ = Real.exp (∑ i, (hH.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
      _ = 1 := by rw [sum_sub_distrib, htr']; simp
  have hprod : 0 < ∏ i, (G i i)⁻¹ := prod_pos fun i _ => inv_pos.mpr (hd i)
  have : G.det * ∏ i, (G i i)⁻¹ ≤ 1 := by rw [← hdetM, hdet]; exact hle
  have hP : (∏ i, G i i) * ∏ i, (G i i)⁻¹ = 1 := by
    rw [← prod_mul_distrib]; exact prod_eq_one fun i _ => mul_inv_cancel₀ (hd i).ne'
  calc G.det = G.det * (∏ i, (G i i)⁻¹) * ∏ i, G i i := by
        rw [mul_assoc, mul_comm (∏ i, (G i i)⁻¹), hP, mul_one]
    _ ≤ 1 * ∏ i, G i i := by
        apply mul_le_mul_of_nonneg_right this (prod_nonneg fun i _ => (hd i).le)
    _ = ∏ i, G i i := one_mul _

end PierceBound
