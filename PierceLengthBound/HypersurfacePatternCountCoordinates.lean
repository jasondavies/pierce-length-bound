/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCountLattice
public import PierceLengthBound.LatticeExterior

/-! # Reduced coordinates for the cross-congruence polynomial fibers -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

lemma det3_cyclic (x y z : Fin 3 → ℤ) : det3 y z x = det3 x y z := by
  unfold det3
  ring

lemma det3_eq_dot_cross3 (x y z : Fin 3 → ℤ) : det3 x y z = dot3 x (cross3 y z) := by
  simp only [det3, dot3, cross3_zero, cross3_one, cross3_two]
  ring

lemma cross3_ne_zero_of_det3 {x y z : Fin 3 → ℤ} (hd : det3 x y z ≠ 0) :
    cross3 y z ≠ 0 := by
  intro h
  apply hd
  rw [det3_eq_dot_cross3, h]
  simp [dot3]

/-- A reduced basis of a lattice containing `nℤ³` has each vector of length at most
`8n/√27`. This first-coordinate version is applied cyclically below. -/
lemma reduced_basis_first_norm_le {Λ : AddSubgroup (Fin 3 → ℤ)} {n : ℕ} (hn : 0 < n)
    (hΛ : ∀ x : Fin 3 → ℤ, (∀ j, (n : ℤ) ∣ x j) → x ∈ Λ)
    {b1 b2 b3 : Fin 3 → ℤ} (hD : det3 b1 b2 b3 ≠ 0)
    (hdvd : ∀ w ∈ Λ, det3 b1 b2 b3 ∣ det3 w b2 b3 ∧
      det3 b1 b2 b3 ∣ det3 b1 w b3 ∧ det3 b1 b2 b3 ∣ det3 b1 b2 w)
    (hred : 27 * (nrm3 b1 * nrm3 b2 * nrm3 b3) ≤ 64 * det3 b1 b2 b3 ^ 2) :
    27 * nrm3 b1 ≤ 64 * (n : ℤ) ^ 2 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, cross3 b2 b3 j ≠ 0 := by
    by_contra h
    push Not at h
    exact cross3_ne_zero_of_det3 hD (funext h)
  let w : Fin 3 → ℤ := Pi.single j n
  have hwΛ : w ∈ Λ := hΛ w (fun k => by simp [w, Pi.single_apply]; split_ifs <;> simp)
  have hnorm : nrm3 w = (n : ℤ) ^ 2 := by
    fin_cases j <;> simp [w, nrm3, dot3] <;> ring
  have hdet : det3 w b2 b3 = n * cross3 b2 b3 j := by
    fin_cases j <;> simp [w, det3, cross3]
    ring
  have hdw : det3 w b2 b3 ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (by exact_mod_cast hn.ne') hj
  obtain ⟨y, hy, hy1, _, _⟩ := reduced_coords hD (hdvd w hwΛ) hred
  have he : det3 w b2 b3 = y 0 * det3 b1 b2 b3 := by
    rw [hy]
    simp only [det3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hy0 : y 0 ≠ 0 := by intro hz; apply hdw; rw [he, hz, zero_mul]
  have hy01 : 1 ≤ y 0 ^ 2 := by nlinarith [sq_pos_of_ne_zero hy0]
  rw [hnorm] at hy1
  have := mul_le_mul_of_nonneg_left hy01 (nrm3_nonneg b1)
  nlinarith

theorem reduced_basis_norm_le {Λ : AddSubgroup (Fin 3 → ℤ)} {n : ℕ} (hn : 0 < n)
    (hΛ : ∀ x : Fin 3 → ℤ, (∀ j, (n : ℤ) ∣ x j) → x ∈ Λ)
    {b1 b2 b3 : Fin 3 → ℤ} (hD : det3 b1 b2 b3 ≠ 0)
    (hdvd : ∀ w ∈ Λ, det3 b1 b2 b3 ∣ det3 w b2 b3 ∧
      det3 b1 b2 b3 ∣ det3 b1 w b3 ∧ det3 b1 b2 b3 ∣ det3 b1 b2 w)
    (hred : 27 * (nrm3 b1 * nrm3 b2 * nrm3 b3) ≤ 64 * det3 b1 b2 b3 ^ 2) :
    27 * nrm3 b1 ≤ 64 * (n : ℤ) ^ 2 ∧
    27 * nrm3 b2 ≤ 64 * (n : ℤ) ^ 2 ∧
    27 * nrm3 b3 ≤ 64 * (n : ℤ) ^ 2 := by
  have h2 : det3 b2 b3 b1 ≠ 0 := by rwa [det3_cyclic]
  have hd2 : ∀ w ∈ Λ, det3 b2 b3 b1 ∣ det3 w b3 b1 ∧
      det3 b2 b3 b1 ∣ det3 b2 w b1 ∧ det3 b2 b3 b1 ∣ det3 b2 b3 w := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hdvd w hw
    exact ⟨by simpa only [det3_cyclic w b3 b1, det3_cyclic b1 w b3,
      det3_cyclic b1 b2 b3] using h2,
      by simpa only [det3_cyclic b1 b2 w, det3_cyclic b1 b2 b3] using h3,
      by simpa only [det3_cyclic w b2 b3, det3_cyclic b1 b2 b3] using h1⟩
  have hr2 : 27 * (nrm3 b2 * nrm3 b3 * nrm3 b1) ≤ 64 * det3 b2 b3 b1 ^ 2 := by
    rw [det3_cyclic]
    nlinarith [hred]
  have h3 : det3 b3 b1 b2 ≠ 0 := by rwa [det3_cyclic]
  have hd3 : ∀ w ∈ Λ, det3 b3 b1 b2 ∣ det3 w b1 b2 ∧
      det3 b3 b1 b2 ∣ det3 b3 w b2 ∧ det3 b3 b1 b2 ∣ det3 b3 b1 w := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hdvd w hw
    exact ⟨by simpa only [det3_cyclic b2 b3 b1, det3_cyclic b1 b2 b3,
      ← det3_cyclic w b1 b2] using h3,
      by simpa only [det3_cyclic b2 b3 b1, det3_cyclic b1 b2 b3,
        det3_cyclic b3 w b2] using h1,
      by simpa only [det3_cyclic b2 b3 b1, det3_cyclic b1 b2 b3,
        det3_cyclic b3 b1 w] using h2⟩
  have hr3 : 27 * (nrm3 b3 * nrm3 b1 * nrm3 b2) ≤ 64 * det3 b3 b1 b2 ^ 2 := by
    rw [det3_cyclic, det3_cyclic]
    nlinarith [hred]
  exact ⟨reduced_basis_first_norm_le hn hΛ hD hdvd hred,
    reduced_basis_first_norm_le hn hΛ h2 hd2 hr2,
    reduced_basis_first_norm_le hn hΛ h3 hd3 hr3⟩

/-- The existing integer-coordinate construction, retaining its individual norm weights. -/
theorem reduced_ycoord_norm_bound {b1 b2 b3 w : Fin 3 → ℤ}
    (hD : det3 b1 b2 b3 ≠ 0)
    (hdvd : det3 b1 b2 b3 ∣ det3 w b2 b3 ∧
      det3 b1 b2 b3 ∣ det3 b1 w b3 ∧ det3 b1 b2 b3 ∣ det3 b1 b2 w)
    (hred : 27 * (nrm3 b1 * nrm3 b2 * nrm3 b3) ≤ 64 * det3 b1 b2 b3 ^ 2)
    (i : Fin 3) :
    27 * (nrm3 (![b1, b2, b3] i) * ycoord b1 b2 b3 w i ^ 2) ≤ 64 * nrm3 w := by
  obtain ⟨y, hy, hy0, hy1, hy2⟩ := reduced_coords hD hdvd hred
  have hyj : ∀ j, w j = y 0 * b1 j + y 1 * b2 j + y 2 * b3 j := fun j => by
    rw [hy]
    simp [mul_comm]
  have hyc : ycoord b1 b2 b3 w = y := by
    have d0 : det3 w b2 b3 = y 0 * det3 b1 b2 b3 := by
      simp only [det3]; rw [hyj 0, hyj 1, hyj 2]; ring
    have d1 : det3 b1 w b3 = y 1 * det3 b1 b2 b3 := by
      simp only [det3]; rw [hyj 0, hyj 1, hyj 2]; ring
    have d2 : det3 b1 b2 w = y 2 * det3 b1 b2 b3 := by
      simp only [det3]; rw [hyj 0, hyj 1, hyj 2]; ring
    funext j
    fin_cases j <;> simp [ycoord, d0, d1, d2, Int.mul_ediv_cancel _ hD]
  rw [hyc]
  fin_cases i
  · exact hy0
  · exact hy1
  · exact hy2

/-- An integral coordinate in a reduced basis is at most `3X` divided by the corresponding
basis-vector length. -/
theorem reduced_ycoord_real_bound {b1 b2 b3 w : Fin 3 → ℤ} {X : ℕ}
    (hD : det3 b1 b2 b3 ≠ 0)
    (hdvd : det3 b1 b2 b3 ∣ det3 w b2 b3 ∧
      det3 b1 b2 b3 ∣ det3 b1 w b3 ∧ det3 b1 b2 b3 ∣ det3 b1 b2 w)
    (hred : 27 * (nrm3 b1 * nrm3 b2 * nrm3 b3) ≤ 64 * det3 b1 b2 b3 ^ 2)
    (hw : ∀ j, |w j| ≤ X) (i : Fin 3) :
    Real.sqrt (nrm3 (![b1, b2, b3] i) : ℝ) * |(ycoord b1 b2 b3 w i : ℝ)| ≤ 3 * X := by
  have hb := reduced_ycoord_norm_bound hD hdvd hred i
  have hn := nrm3_le_of_abs_le hw
  have hnorm : (0 : ℝ) ≤ nrm3 (![b1, b2, b3] i) := by
    exact_mod_cast nrm3_nonneg _
  have hs := Real.sq_sqrt hnorm
  have hbR : 27 * ((nrm3 (![b1, b2, b3] i) : ℝ) *
      (ycoord b1 b2 b3 w i : ℝ) ^ 2) ≤ 64 * (nrm3 w : ℝ) := by exact_mod_cast hb
  have hnR : (nrm3 w : ℝ) ≤ 3 * (X : ℝ) ^ 2 := by exact_mod_cast hn
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, hs, sq_abs]
  nlinarith [sq_nonneg (X : ℝ)]

end
end PierceLengthBound.FixedDividend
