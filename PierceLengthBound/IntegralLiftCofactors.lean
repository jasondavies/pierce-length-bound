/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicCofactors
public import PierceLengthBound.ConicReconstruction

/-! Reconstruction of the orbit quotient `q_i` and the moments `h_i(j)`, `j ≤ 8`, from the
signed maximal minors of a linearly independent `8 × 9` system annihilating the moment vector.
Here the system is a hypothesis; `IntegralLiftMomentSystem` constructs it for the orbit. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Matrix

/-- Two normalized moments reconstruct every kernel coordinate from maximal
minors. Positivity of the variance proves both displayed denominators nonzero. -/
theorem cofactor_normalized_reconstruction
    (c v : Fin 9 → ℝ) {q : ℝ} (hc : c 0 ≠ 0) (hv : 0 < v 0)
    (hprop : ∀ j, c 0 * v j = v 0 * c j)
    (hvar : v 1 ^ 2 < v 0 * v 2)
    (h1 : q * v 0 + v 1 = 1) (h2 : q * v 1 + v 2 = 1) :
    c 1 - c 0 ≠ 0 ∧ c 1 ^ 2 - c 0 * c 2 ≠ 0 ∧
      q = (c 1 - c 2) / (c 1 - c 0) ∧
      ∀ j, v j = c j * (c 1 - c 0) / (c 1 ^ 2 - c 0 * c 2) := by
  have hp1 := hprop 1
  have hp2 := hprop 2
  have hv10 : v 1 ≠ v 0 := by
    intro he
    have : v 2 = v 0 := by rw [he] at h2; linarith
    rw [he, this] at hvar
    nlinarith
  have hd1 : c 1 - c 0 ≠ 0 := by
    intro hz
    have he := sub_eq_zero.mp hz
    rw [he] at hp1
    apply hv10
    exact (mul_left_cancel₀ hc (by simpa only [mul_comm] using hp1))
  have hdet : (v 0) ^ 2 * (c 1 ^ 2 - c 0 * c 2) =
      (c 0) ^ 2 * (v 1 ^ 2 - v 0 * v 2) := by
    linear_combination -(c 0 * v 1 + v 0 * c 1) * hp1 + c 0 * v 0 * hp2
  have hd2 : c 1 ^ 2 - c 0 * c 2 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hdet
    have hc2 : 0 < (c 0) ^ 2 := sq_pos_of_ne_zero hc
    nlinarith
  have hq : q * (c 1 - c 0) = c 1 - c 2 := by
    have he : v 0 * (q * (c 1 - c 0) - (c 1 - c 2)) = 0 := by
      linear_combination c 0 * (h2 - h1) - q * hp1 - hp2 + hp1
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hv.ne')
  have hscale : v 0 * (c 1 ^ 2 - c 0 * c 2) = c 0 * (c 1 - c 0) := by
    linear_combination -c 1 * hp1 + c 0 * hp2 +
      c 0 * c 1 * h1 - (c 0) ^ 2 * h2 + q * c 0 * hp1
  refine ⟨hd1, hd2, (eq_div_iff hd1).mpr hq, fun j => ?_⟩
  apply (eq_div_iff hd2).mpr
  apply mul_left_cancel₀ hc
  linear_combination (c 1 ^ 2 - c 0 * c 2) * hprop j + c j * hscale

/-- At an orbit state `i` with `i + 1 < P(a,b)`, every linearly independent `8 × 9` system
annihilating `(h_i(j))_{j ≤ 8}` has cofactors `c` with `c₀ ≠ 0`,
`q_i = (c₁ - c₂) / (c₁ - c₀)` and `h_i(j) = c_j (c₁ - c₀) / (c₁² - c₀ c₂)`. -/
theorem orbit_cofactor_reconstruction {a b i : ℕ} (hba : b < a)
    (hi : i + 1 < P a b) (M : Matrix (Fin 8) (Fin 9) ℝ)
    (hM : LinearIndependent ℝ M.row)
    (hker : M *ᵥ (fun j => hm a b i j.val) = 0) :
    let c := momentCofactors M
    c 0 ≠ 0 ∧ c 1 - c 0 ≠ 0 ∧ c 1 ^ 2 - c 0 * c 2 ≠ 0 ∧
      (qq a b i : ℝ) = (c 1 - c 2) / (c 1 - c 0) ∧
      ∀ j : Fin 9, hm a b i j.val =
        c j * (c 1 - c 0) / (c 1 ^ 2 - c 0 * c 2) := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb : (0 : ℝ) < orb a b i := by
    exact_mod_cast orb_pos_of_lt (by omega : i < P a b)
  have hv : 0 < hm a b i 0 := by
    rw [hm_zero hba (P a b - 1 - i) i (by omega)]
    positivity
  have hd := momentTail_det_ne_zero M hM (fun j => hm a b i j.val) hker hv.ne'
  have hc : momentCofactors M 0 ≠ 0 := by
    simpa only [momentCofactors, Fin.cons_zero] using hd
  obtain ⟨h1, h2⟩ := orbit_moment_normalizations hba hi
  exact ⟨hc, cofactor_normalized_reconstruction (momentCofactors M)
    (fun j => hm a b i j.val) hc hv (momentCofactors_proportional M hd _ hker)
      (orbit_moment_variance hba hi) h1 h2⟩

end
end PierceLengthBound.FixedDividend
