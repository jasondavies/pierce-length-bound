/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Tactic

/-!
# The resultant of consecutive orthogonal polynomials

The algebraic recurrence is proved here. Establishing the three-term recurrence for the
Pierce moment functional and identifying its coefficients with Hankel determinant ratios
remain separate obligations.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

open Polynomial

/-- One step of the three-term recurrence, with explicit Sylvester matrix sizes. -/
lemma resultant_step {p r q : ℝ[X]} {n : ℕ} {α β : ℝ}
    (hp : p.natDegree ≤ n) (hr : r.natDegree ≤ n + 1) (hrc : r.coeff (n + 1) = 1)
    (hq : q = C (-β) * p + r * (X - C α)) :
    resultant r q (n + 1) (n + 2) =
      (-β) ^ (n + 1) * resultant r p (n + 1) n := by
  have hlin : (X - C α : ℝ[X]).natDegree ≤ 1 := by compute_degree!
  rw [hq, resultant_add_mul_right r (C (-β) * p) (X - C α) (n + 1) (n + 2)
    (by omega) hr,
    resultant_C_mul_right]
  rw [resultant_add_right_deg r p (n + 1) n 2 hp, hrc]
  simp

/-- Rank-four specialization of the recurrence product. -/
theorem resultant_four {p : ℕ → ℝ[X]} {α β : ℕ → ℝ}
    (h0 : p 0 = 1)
    (hdeg : ∀ j ≤ 4, (p j).natDegree ≤ j)
    (hlead : ∀ j ≤ 4, (p j).coeff j = 1)
    (hrec : ∀ j < 4, p (j + 2) = C (-β (j + 1)) * p j +
      p (j + 1) * (X - C (α (j + 1)))) :
    resultant (p 4) (p 5) 4 5 = β 1 * β 2 ^ 2 * β 3 ^ 3 * β 4 ^ 4 := by
  have h1 := resultant_step (hdeg 0 (by omega)) (hdeg 1 (by omega))
    (hlead 1 (by omega)) (hrec 0 (by omega))
  have h2 := resultant_step (hdeg 1 (by omega)) (hdeg 2 (by omega))
    (hlead 2 (by omega)) (hrec 1 (by omega))
  have h3 := resultant_step (hdeg 2 (by omega)) (hdeg 3 (by omega))
    (hlead 3 (by omega)) (hrec 2 (by omega))
  have h4 := resultant_step (hdeg 3 (by omega)) (hdeg 4 (by omega))
    (hlead 4 (by omega)) (hrec 3 (by omega))
  norm_num at h1 h2 h3 h4
  simp only [h0, coeff_one, ite_true, mul_one] at h1
  rw [resultant_comm (p 2) (p 1) 2 1, h1] at h2
  rw [resultant_comm (p 3) (p 2) 3 2, h2] at h3
  rw [resultant_comm (p 4) (p 3) 4 3, h3] at h4
  convert h4 using 1
  ring

end PierceLengthBound.FixedDividend
