/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCountFiber

/-! # Removing the common factor from an integral first vertex -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open scoped Matrix
noncomputable section

/-- Divide the first vertex by its full common divisor. -/
def primitiveFirstVertex (m : ℕ) (u : Fin 3 → ℤ) : Fin 3 → ℤ :=
  fun j => u j / (gcd4 m u : ℤ)

/-- With `g = gcd(m, u)` and `n = m / g`: `m = g n`, `u = g u'` for the primitive first
vertex `u'`, and `u'` is primitive modulo `n`. -/
lemma primitiveFirstVertex_spec {m : ℕ} (hm : 0 < m) (u : Fin 3 → ℤ) :
    let g := gcd4 m u
    let n := m / g
    0 < g ∧ 0 < n ∧ m = g * n ∧
    (∀ j, u j = (g : ℤ) * primitiveFirstVertex m u j) ∧
    gcd4 n (primitiveFirstVertex m u) = 1 := by
  dsimp only
  have hg : 0 < gcd4 m u := gcd4_pos hm u
  have hd : gcd4 m u ∣ m := gcd4_dvd_m m u
  have hmg : m = gcd4 m u * (m / gcd4 m u) := (Nat.mul_div_cancel' hd).symm
  have hn : 0 < m / gcd4 m u := by
    have : gcd4 m u ≤ m := Nat.le_of_dvd hm hd
    exact Nat.div_pos this hg
  have hu : ∀ j, u j = (gcd4 m u : ℤ) * primitiveFirstVertex m u j := fun j =>
    (Int.mul_ediv_cancel' (gcd4_dvd m u j)).symm
  refine ⟨hg, hn, hmg, hu, ?_⟩
  obtain ⟨a, c0, c1, c2, hb⟩ := gcd4_bezout m u
  have hb' : (m / gcd4 m u : ℕ) * a + primitiveFirstVertex m u 0 * c0 +
      primitiveFirstVertex m u 1 * c1 + primitiveFirstVertex m u 2 * c2 = (1 : ℤ) := by
    apply mul_left_cancel₀ (show (gcd4 m u : ℤ) ≠ 0 by exact_mod_cast hg.ne')
    have hmZ : (m : ℤ) = gcd4 m u * (m / gcd4 m u : ℕ) := by exact_mod_cast hmg
    rw [hmZ, hu 0, hu 1, hu 2] at hb
    linear_combination hb
  have hmdiv : (gcd4 (m / gcd4 m u) (primitiveFirstVertex m u) : ℤ) ∣
      (m / gcd4 m u : ℕ) := by
    exact_mod_cast gcd4_dvd_m (m / gcd4 m u) (primitiveFirstVertex m u)
  have hd1 : (gcd4 (m / gcd4 m u) (primitiveFirstVertex m u) : ℤ) ∣ 1 := by
    rw [← hb']
    exact dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_left hmdiv a)
      (dvd_mul_of_dvd_left (gcd4_dvd _ _ 0) c0))
      (dvd_mul_of_dvd_left (gcd4_dvd _ _ 1) c1))
      (dvd_mul_of_dvd_left (gcd4_dvd _ _ 2) c2)
  exact Nat.dvd_one.mp (by exact_mod_cast hd1)

lemma primitiveFirstVertex_mem_ibox {m : ℕ} (hm : 0 < m) {u : Fin 3 → ℤ}
    (hu : u ∈ ibox3 m) : primitiveFirstVertex m u ∈ ibox3 (m / gcd4 m u) := by
  obtain ⟨hg, _, hmgn, he, _⟩ := primitiveFirstVertex_spec hm u
  apply Fintype.mem_piFinset.mpr
  intro j
  have hbox := abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hu j))
  have hgZ : (0 : ℤ) < gcd4 m u := by exact_mod_cast hg
  have hmZ : (m : ℤ) = gcd4 m u * (m / gcd4 m u : ℕ) := by exact_mod_cast hmgn
  rw [he j, abs_mul, abs_of_pos hgZ, hmZ] at hbox
  exact Finset.mem_Icc.mpr (abs_le.mp ((mul_le_mul_iff_right₀ hgZ).mp hbox))

/-- Dividing by the common factor preserves exactly the cross-congruence. -/
theorem primitiveFirstVertex_cross_iff {m : ℕ} (hm : 0 < m) (u v : Fin 3 → ℤ) :
    (∀ j, (m : ℤ) ∣ (u ⨯₃ v) j) ↔
      ∀ j, ((m / gcd4 m u : ℕ) : ℤ) ∣ (primitiveFirstVertex m u ⨯₃ v) j := by
  obtain ⟨hg, _, hmgn, he, _⟩ := primitiveFirstVertex_spec hm u
  have hmZ : (m : ℤ) = gcd4 m u * (m / gcd4 m u : ℕ) := by exact_mod_cast hmgn
  have hc j : (u ⨯₃ v) j = (gcd4 m u : ℤ) * (primitiveFirstVertex m u ⨯₃ v) j := by
    simp only [cross_apply_cyc, he]
    ring
  simp only [hmZ, hc, mul_dvd_mul_iff_left (show (gcd4 m u : ℤ) ≠ 0 by
    exact_mod_cast hg.ne')]

/-- The fiber bound for an arbitrary first vertex `u`: with `g = gcd(m, u)`, a nonzero
`f` vanishes on at most `243 D X² / ((m/g) μ)` solutions of `u × v ≡ 0 (mod m)` in
`[-X, X]³`, where `μ = normalShortR (m/g) (u/g)`. -/
theorem cross_congruence_polynomial_fiber_count {m X : ℕ} (hm : 0 < m) (hX : m ≤ X)
    (u : Fin 3 → ℤ) {f : MvPolynomial (Fin 3) ℚ} (hf : f ≠ 0) :
    (((ibox3 X).filter fun v => (∀ j, (m : ℤ) ∣ (u ⨯₃ v) j) ∧
      MvPolynomial.eval (fun i => (v i : ℚ)) f = 0).card : ℝ) ≤
      243 * f.totalDegree * (X : ℝ) ^ 2 /
        ((m / gcd4 m u : ℕ) * (normalShortR (m / gcd4 m u) (primitiveFirstVertex m u) : ℝ)) := by
  obtain ⟨_, hn, _, _, hprimitive⟩ := primitiveFirstVertex_spec hm u
  have hnX : m / gcd4 m u ≤ X := (Nat.div_le_self _ _).trans hX
  simpa only [← primitiveFirstVertex_cross_iff hm u] using
    primitive_cross_congruence_polynomial_fiber_count hn hnX
      (primitiveFirstVertex m u) hprimitive hf

end
end PierceLengthBound.FixedDividend
