/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCountPolynomial
public import PierceLengthBound.HypersurfacePatternCountGrid

/-! # Polynomial zeros among divisible first vertices -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

def ibox4 (X : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(X : ℤ)) X

/-- The ordinary four-variable polynomial grid estimate, with rational coefficients. -/
theorem polynomial_ibox4_count {q : MvPolynomial (Fin 4) ℚ} (hq : q ≠ 0)
    {R : ℕ} (hR : 1 ≤ R) :
    (((ibox4 R).filter fun x => eval (fun i => (x i : ℚ)) q = 0).card : ℝ) ≤
      27 * q.totalDegree * (R : ℝ) ^ 3 := by
  classical
  let S := rationalIntegerInterval (R : ℝ)
  let Z := (Fintype.piFinset fun _ : Fin 4 => S).filter fun x => eval x q = 0
  have hS : S.Nonempty := rationalIntegerInterval_nonempty (by positivity)
  have hS0 : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hs := schwartz_zippel_totalDegree hq S
  have hsR : (Z.card : ℝ) / (S.card : ℝ) ^ 4 ≤ (q.totalDegree : ℝ) / S.card := by
    have h := (NNRat.cast_le (K := ℝ)).mpr hs
    simpa [NNRat.cast_div, NNRat.cast_pow, NNRat.cast_natCast] using h
  have hz : (Z.card : ℝ) ≤ q.totalDegree * (S.card : ℝ) ^ 3 := by
    have h := (div_le_iff₀ (pow_pos hS0 4)).mp hsR
    convert h using 1
    field_simp
  have hcard : (((ibox4 R).filter fun x => eval (fun i => (x i : ℚ)) q = 0).card : ℝ) ≤
      Z.card := by
    exact_mod_cast Finset.card_le_card_of_injOn (fun x : Fin 4 → ℤ => fun i => (x i : ℚ))
      (t := Z) (fun x hx => by
        obtain ⟨hxbox, hxq⟩ := Finset.mem_filter.mp hx
        refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => ?_), hxq⟩
        apply mem_rationalIntegerInterval
        exact_mod_cast abs_le.mpr
          (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hxbox i)))
      (fun x _ y _ h => by
        funext i
        have hi : (x i : ℚ) = (y i : ℚ) := congrFun h i
        exact_mod_cast hi)
  have hcS : (S.card : ℝ) ≤ 3 * R := rationalIntegerInterval_card (by exact_mod_cast hR)
  calc _ ≤ (q.totalDegree : ℝ) * (S.card : ℝ) ^ 3 := hcard.trans hz
    _ ≤ (q.totalDegree : ℝ) * (3 * (R : ℝ)) ^ 3 := by gcongr
    _ = _ := by ring

/-- Divisibility scales a four-dimensional box down exactly. -/
lemma ediv_mem_ibox4 {g X : ℕ} (hg : 0 < g) {x : Fin 4 → ℤ} (hx : x ∈ ibox4 X)
    (hd : ∀ i, (g : ℤ) ∣ x i) : (fun i => x i / (g : ℤ)) ∈ ibox4 (X / g) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hx' := abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hx i))
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have he : x i = (g : ℤ) * (x i / (g : ℤ)) := (Int.mul_ediv_cancel' (hd i)).symm
  have hb : (g : ℤ) * |x i / (g : ℤ)| ≤ X := by
    rw [he, abs_mul, abs_of_pos hgZ] at hx'
    exact hx'
  have hab : |x i / (g : ℤ)| ≤ (X : ℤ) / g :=
    (Int.le_ediv_iff_mul_le hgZ).mpr (by simpa [mul_comm] using hb)
  rw [← Int.natCast_div] at hab
  exact Finset.mem_Icc.mpr (abs_le.mp hab)

/-- The number of zero first vertices divisible by `g` is `O(D (X/g)^3)`.
Scaling the polynomial preserves nonzeroness, so this is uniform in `g`. -/
theorem polynomial_divisible_ibox4_count {q : MvPolynomial (Fin 4) ℚ} (hq : q ≠ 0)
    {g X : ℕ} (hg : 0 < g) (hgX : g ≤ X) :
    (((ibox4 X).filter fun x => (∀ i, (g : ℤ) ∣ x i) ∧
      eval (fun i => (x i : ℚ)) q = 0).card : ℝ) ≤
      27 * q.totalDegree * (X / g : ℕ) ^ 3 := by
  classical
  let r : MvPolynomial (Fin 4) ℚ := aeval (fun i => C (g : ℚ) * MvPolynomial.X i) q
  have hr : r ≠ 0 := scalar_substitution_ne_zero hq (by exact_mod_cast hg.ne')
  have hdeg : r.totalDegree ≤ q.totalDegree := scalar_substitution_degree q g
  let Z := (ibox4 (X / g)).filter fun x => eval (fun i => (x i : ℚ)) r = 0
  have hc : (((ibox4 X).filter fun x => (∀ i, (g : ℤ) ∣ x i) ∧
      eval (fun i => (x i : ℚ)) q = 0).card : ℝ) ≤ Z.card := by
    exact_mod_cast Finset.card_le_card_of_injOn (fun x : Fin 4 → ℤ => fun i => x i / (g : ℤ))
      (t := Z) (fun x hx => by
        obtain ⟨hxbox, hd, hxq⟩ := Finset.mem_filter.mp hx
        refine Finset.mem_filter.mpr ⟨ediv_mem_ibox4 hg hxbox hd, ?_⟩
        rw [show r = aeval (fun i => C (g : ℚ) * MvPolynomial.X i) q from rfl,
          eval_scalar_substitution]
        convert hxq using 2
        congr 1
        funext i
        exact_mod_cast Int.mul_ediv_cancel' (hd i))
      (fun x hx y hy he => by
        have hdx := (Finset.mem_filter.mp hx).2.1
        have hdy := (Finset.mem_filter.mp hy).2.1
        funext i
        have hi : x i / (g : ℤ) = y i / (g : ℤ) := congrFun he i
        calc x i = (g : ℤ) * (x i / (g : ℤ)) := (Int.mul_ediv_cancel' (hdx i)).symm
          _ = (g : ℤ) * (y i / (g : ℤ)) := by rw [hi]
          _ = y i := Int.mul_ediv_cancel' (hdy i))
  have hz := polynomial_ibox4_count hr (Nat.div_pos hgX hg)
  exact hc.trans (hz.trans (by gcongr))

end
end PierceLengthBound.FixedDividend
