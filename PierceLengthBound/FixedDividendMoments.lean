/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.MinorHeight

/-!
# Moment identities for the fixed-dividend refinement

The support conditions are explicit. In particular the terminal point mass is never
assigned the nonterminal first moment.
-/

@[expose] public section

namespace PierceLengthBound

open Finset Polynomial

variable {a b : ℕ}

lemma nuF_add (i : ℕ) (f g : ℝ[X]) :
    nuF a b i (f + g) = nuF a b i f + nuF a b i g := by
  simp [nuF, mul_add, add_div, sum_add_distrib]

/-- Multiplication by `X + qᵢ` converts the weighted functional into the probability one. -/
lemma nuF_q_mul (hba : b < a) (i : ℕ) (f : ℝ[X]) :
    nuF a b i ((X + C (qq a b i : ℝ)) * f) = muF a b i f := by
  unfold nuF muF
  refine sum_congr rfl fun j hj => ?_
  have hq : (qq a b (i + j) : ℝ) ≠ 0 := by
    have hij : i + j < P a b := by have := mem_range.mp hj; omega
    exact_mod_cast (show qq a b (i + j) ≠ 0 by have := qq_pos hba hij; omega)
  rw [eval_mul, eval_add, eval_X, eval_C, ← qq_eq_add_pt]
  field_simp

/-- Weighted functional shift, including the quotient in the denominator. -/
lemma nuF_X_mul {i : ℕ} (hl : i + 1 < P a b) (g : ℝ[X]) :
    nuF a b i (X * g) = nuF a b (i + 1) (g.comp (X + C (kk a b i))) := by
  unfold nuF
  rw [show P a b - i = (P a b - (i + 1)) + 1 by omega, sum_range_succ', pt_zero]
  simp only [eval_mul, eval_X, zero_mul, mul_zero, zero_div, add_zero]
  refine sum_congr rfl fun j hj => ?_
  have hp : 0 < pt a b i (j + 1) := by
    have := pt_ge (a := a) (b := b) (i := i) (j := j + 1)
      (by have := mem_range.mp hj; omega)
    push_cast at this
    linarith
  rw [wt_of_lt a b hl, ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel,
    eval_comp, eval_add, eval_X, eval_C, pt_succ, kk]
  rw [show i + (j + 1) = i + 1 + j by omega]
  rw [pt_succ] at hp
  congr 1
  field_simp
  ring_nf

/-- Iterating the weighted shift through the Newton basis. -/
lemma nuF_nb_mul : ∀ (j i : ℕ), i + j < P a b → ∀ g : ℝ[X],
    nuF a b i (nb a b i j * g) =
      nuF a b (i + j) (g.comp (X + C (pt a b i j))) := by
  intro j
  induction j with
  | zero => intro i _ g; simp [nb, pt]
  | succ j ih =>
    intro i hij g
    rw [nb_succ, mul_assoc, nuF_X_mul (by omega), mul_comp, comp_shift_cancel,
      ih (i + 1) (by omega), show i + 1 + j = i + (j + 1) by ring, comp_assoc]
    congr 2
    simp only [add_comp, X_comp, C_comp, pt_succ, kk, map_add]
    ring

lemma nuF_nb (hba : b < a) {i j : ℕ} (hij : i + j < P a b) :
    nuF a b i (nb a b i j) = (orb a b (i + j) : ℝ) / a := by
  rw [← mul_one (nb a b i j), nuF_nb_mul j i hij, one_comp, nuF_one hba hij]

lemma muF_nb (hba : b < a) {i j : ℕ} (hij : i + j < P a b) :
    muF a b i (nb a b i j) = 1 := by
  rw [← mul_one (nb a b i j), muF_nb_mul j i hij, one_comp, muF_one hba hij]

lemma muF_nb_X (hba : b < a) {i j : ℕ} (hij : i + j + 1 < P a b) :
    muF a b i (nb a b i j * X) = pt a b i j + 1 := by
  rw [muF_nb_mul j i (by omega), X_comp, muF_add, muF_X hba hij, muF_C,
    muF_one hba (by omega)]
  ring

lemma muF_nb_sq_X (hba : b < a) {i j : ℕ} (hij : i + j + 2 < P a b) :
    muF a b i (nb a b i j * X ^ 2) =
      pt a b i j ^ 2 + 2 * pt a b i j + kk a b (i + j) + 1 := by
  rw [muF_nb_mul j i (by omega), pow_comp, X_comp, muF_shift_sq hba hij]

lemma muF_nb_cube_X (hba : b < a) {i j : ℕ} (hij : i + j + 3 < P a b) :
    muF a b i (nb a b i j * X ^ 3) =
      pt a b i j ^ 3 + 3 * pt a b i j ^ 2 + 3 * pt a b i j * (kk a b (i + j) + 1) +
        (kk a b (i + j) ^ 2 + 2 * kk a b (i + j) + kk a b (i + j + 1) + 1) := by
  rw [muF_nb_mul j i (by omega), pow_comp, X_comp, muF_shift_cube hba hij]


lemma muF_sum {ι : Type*} (s : Finset ι) (i : ℕ) (f : ι → ℝ[X]) :
    muF a b i (∑ t ∈ s, f t) = ∑ t ∈ s, muF a b i (f t) := by
  simp only [muF, eval_finsetSum, mul_sum]
  exact sum_comm

/-- A linear combination in the first five Newton basis polynomials. -/
noncomputable def newtonQuartic (a b i : ℕ) (c : Fin 5 → ℝ) : ℝ[X] :=
  ∑ j : Fin 5, C (c j) * nb a b i j

lemma nuF_newtonQuartic (i : ℕ) (c : Fin 5 → ℝ) :
    nuF a b i (newtonQuartic a b i c) = ∑ j : Fin 5, c j * nuF a b i (nb a b i j) := by
  rw [newtonQuartic, nuF_sum]
  exact sum_congr rfl fun j _ => nuF_C_mul i (c j) (nb a b i j)

lemma muF_newtonQuartic_mul (i : ℕ) (c : Fin 5 → ℝ) (g : ℝ[X]) :
    muF a b i (newtonQuartic a b i c * g) =
      ∑ j : Fin 5, c j * muF a b i (nb a b i j * g) := by
  rw [newtonQuartic, sum_mul, muF_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_assoc, muF_C_mul]

/-- The weighted moment recurrence for an arbitrary polynomial. -/
lemma nuF_mul_X_add (hba : b < a) (i : ℕ) (f : ℝ[X]) :
    nuF a b i (f * X) + (qq a b i : ℝ) * nuF a b i f = muF a b i f := by
  have h := nuF_q_mul hba i f
  rw [show (X + C (qq a b i : ℝ)) * f = f * X + C (qq a b i : ℝ) * f by ring,
    nuF_add, nuF_C_mul] at h
  exact h

/-- The four row/moment equations imply orthogonality to all monomials of degree at most
three. The coefficients need not be specialized to a minor pattern for this lemma. -/
theorem newtonQuartic_orthogonal (hba : b < a) {i : ℕ} (hi : i + 6 < P a b)
    (c : Fin 5 → ℝ)
    (hc0 : ∑ j : Fin 5, c j = 0)
    (hc1 : ∑ j : Fin 5, c j * pt a b i j = 0)
    (hc2 : ∑ j : Fin 5, c j * (pt a b i j ^ 2 + kk a b (i + j)) = 0)
    (hcb : ∑ j : Fin 5, c j * ((orb a b (i + j) : ℝ) / a) = 0) :
    ∀ m < 4, nuF a b i (newtonQuartic a b i c * X ^ m) = 0 := by
  set f := newtonQuartic a b i c
  have hn : nuF a b i f = 0 := by
    rw [nuF_newtonQuartic]
    calc (∑ j : Fin 5, c j * nuF a b i (nb a b i j)) =
        ∑ j : Fin 5, c j * ((orb a b (i + j) : ℝ) / a) := by
          refine sum_congr rfl fun j _ => ?_
          rw [nuF_nb hba (by have := j.isLt; omega)]
      _ = 0 := hcb
  have hm0 : muF a b i f = 0 := by
    rw [← mul_one f, muF_newtonQuartic_mul]
    calc (∑ j : Fin 5, c j * muF a b i (nb a b i j * 1)) = ∑ j : Fin 5, c j := by
          refine sum_congr rfl fun j _ => ?_
          rw [mul_one, muF_nb hba (by have := j.isLt; omega), mul_one]
      _ = 0 := hc0
  have hm1 : muF a b i (f * X) = 0 := by
    rw [muF_newtonQuartic_mul]
    calc (∑ j : Fin 5, c j * muF a b i (nb a b i j * X)) =
        ∑ j : Fin 5, c j * (pt a b i j + 1) := by
          refine sum_congr rfl fun j _ => ?_
          rw [muF_nb_X hba (by have := j.isLt; omega)]
      _ = 0 := by simp only [mul_add, mul_one, sum_add_distrib, hc1, hc0, add_zero]
  have hm2 : muF a b i (f * X ^ 2) = 0 := by
    rw [muF_newtonQuartic_mul]
    calc (∑ j : Fin 5, c j * muF a b i (nb a b i j * X ^ 2)) =
        ∑ j : Fin 5, (c j * (pt a b i j ^ 2 + kk a b (i + j)) +
          2 * (c j * pt a b i j) + c j) := by
          refine sum_congr rfl fun j _ => ?_
          rw [muF_nb_sq_X hba (by have := j.isLt; omega)]
          ring
      _ = 0 := by rw [sum_add_distrib, sum_add_distrib, ← mul_sum, hc2, hc1, hc0]; ring
  have hn1 : nuF a b i (f * X) = 0 := by
    have := nuF_mul_X_add hba i f
    rw [hn, hm0] at this
    linarith
  have hn2 : nuF a b i (f * X ^ 2) = 0 := by
    have := nuF_mul_X_add hba i (f * X)
    rw [show f * X * X = f * X ^ 2 by ring, hn1, hm1] at this
    linarith
  have hn3 : nuF a b i (f * X ^ 3) = 0 := by
    have := nuF_mul_X_add hba i (f * X ^ 2)
    rw [show f * X ^ 2 * X = f * X ^ 3 by ring, hn2, hm2] at this
    linarith
  intro m hm
  interval_cases m
  · simpa only [pow_zero, mul_one] using hn
  · simpa only [pow_one] using hn1
  · exact hn2
  · exact hn3

end PierceLengthBound
