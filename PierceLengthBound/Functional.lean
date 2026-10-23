/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Hankel

/-!
# The moment functionals `μᵢ`, `νᵢ` and the Newton basis

For the moment model of `Hankel.lean` put, for a real polynomial `f`,
`μᵢ(f) = ∑ⱼ wᵢ(j) f(pᵢ(j))` and `νᵢ(f) = ∑ⱼ wᵢ(j) f(pᵢ(j)) / q_{i+j}`, so `νᵢ(Xˢ) = hᵢ(s)`.
With `kᵢ = q_{i+1} - qᵢ` and the Newton basis `Fᵢ,ⱼ = ∏_{l<j} (X - pᵢ(l))`:

* `μᵢ(1) = 1`, `νᵢ(1) = bᵢ/a`;
* the shift `μᵢ(X g) = μ_{i+1}(g(X + kᵢ))`;
* hence `μᵢ(Fᵢ,ⱼ g) = μ_{i+j}(g(X + pᵢ(j)))`;
* `μᵢ(X) = 1`, `μᵢ(X²) = kᵢ + 1`, `μᵢ(X³) = kᵢ² + 2kᵢ + k_{i+1} + 1`;
* `0 ≤ νᵢ(f²) ≤ μᵢ(f²)/qᵢ`.
-/

@[expose] public section

namespace PierceLengthBound

open Finset Polynomial

section Defs

variable (a b : ℕ)

/-- `μᵢ(f) = ∑ⱼ wᵢ(j) f(pᵢ(j))`. -/
noncomputable def muF (i : ℕ) (f : ℝ[X]) : ℝ :=
  ∑ j ∈ range (P a b - i), wt a b i j * f.eval (pt a b i j)

/-- `νᵢ(f) = ∑ⱼ wᵢ(j) f(pᵢ(j)) / q_{i+j}`. -/
noncomputable def nuF (i : ℕ) (f : ℝ[X]) : ℝ :=
  ∑ j ∈ range (P a b - i), wt a b i j * f.eval (pt a b i j) / qq a b (i + j)

/-- The Newton basis `Fᵢ,ⱼ = ∏_{l<j} (X - pᵢ(l))`. -/
noncomputable def nb (i j : ℕ) : ℝ[X] := ∏ l ∈ range j, (X - C (pt a b i l))

end Defs

variable {a b : ℕ}

section Linear

lemma muF_add (i : ℕ) (f g : ℝ[X]) : muF a b i (f + g) = muF a b i f + muF a b i g := by
  simp [muF, mul_add, sum_add_distrib]

lemma muF_C_mul (i : ℕ) (c : ℝ) (f : ℝ[X]) : muF a b i (C c * f) = c * muF a b i f := by
  simp only [muF, eval_mul, eval_C, mul_sum]; refine sum_congr rfl fun j _ => ?_; ring

lemma nuF_C_mul (i : ℕ) (c : ℝ) (f : ℝ[X]) : nuF a b i (C c * f) = c * nuF a b i f := by
  simp only [nuF, eval_mul, eval_C, mul_sum]; refine sum_congr rfl fun j _ => ?_; ring

lemma muF_C (i : ℕ) (c : ℝ) : muF a b i (C c) = c * muF a b i 1 := by
  rw [← mul_one (C c), muF_C_mul]

lemma nuF_sum {ι : Type*} (s : Finset ι) (i : ℕ) (f : ι → ℝ[X]) :
    nuF a b i (∑ t ∈ s, f t) = ∑ t ∈ s, nuF a b i (f t) := by
  simp only [nuF, eval_finsetSum, mul_sum, sum_div]; exact sum_comm

lemma nuF_X_pow (i s : ℕ) : nuF a b i (X ^ s) = hm a b i s := by
  simp [nuF, hm]

end Linear

section Basic

lemma muF_one (hba : b < a) {i : ℕ} (hi : i < P a b) : muF a b i 1 = 1 := by
  simpa [muF] using (wt_spec hba (P a b - 1 - i) i (by omega)).2

lemma nuF_one (hba : b < a) {i : ℕ} (hi : i < P a b) : nuF a b i 1 = orb a b i / a := by
  rw [← pow_zero (X : ℝ[X]), nuF_X_pow]; exact hm_zero hba (P a b - 1 - i) i (by omega)

lemma qq_eq_add_pt (i j : ℕ) : (qq a b (i + j) : ℝ) = pt a b i j + qq a b i := by
  simp [pt]

/-- **The shift** `μᵢ(X g) = μ_{i+1}(g(X + kᵢ))`. -/
lemma muF_X_mul {i : ℕ} (hl : i + 1 < P a b) (g : ℝ[X]) :
    muF a b i (X * g) = muF a b (i + 1) (g.comp (X + C (kk a b i))) := by
  unfold muF
  rw [show P a b - i = (P a b - (i + 1)) + 1 by omega, sum_range_succ', pt_zero]
  simp only [eval_mul, eval_X, zero_mul, mul_zero, add_zero]
  refine sum_congr rfl fun j hj => ?_
  have hp : 0 < pt a b i (j + 1) := by
    have := pt_ge (a := a) (b := b) (i := i) (j := j + 1) (by have := mem_range.mp hj; omega)
    push_cast at this; linarith
  rw [wt_of_lt a b hl, ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel, eval_comp, eval_add,
      eval_X,
    eval_C, pt_succ, kk]
  rw [pt_succ] at hp
  field_simp
  ring_nf

lemma comp_shift_cancel (g : ℝ[X]) (c : ℝ) : (g.comp (X - C c)).comp (X + C c) = g := by
  rw [comp_assoc]; simp

/-- `Fᵢ,ⱼ₊₁ = X · F_{i+1},ⱼ(X - kᵢ)`. -/
lemma nb_succ (i j : ℕ) : nb a b i (j + 1) = X * (nb a b (i + 1) j).comp (X - C (kk a b i)) := by
  unfold nb
  rw [prod_range_succ', pt_zero, map_zero, sub_zero, mul_comm, Polynomial.prod_comp]
  congr 1
  refine prod_congr rfl fun l _ => ?_
  simp only [sub_comp, X_comp, C_comp, pt_succ, kk, map_add]
  ring

/-- `μᵢ(Fᵢ,ⱼ g) = μ_{i+j}(g(X + pᵢ(j)))`. -/
lemma muF_nb_mul : ∀ (j i : ℕ), i + j < P a b → ∀ g : ℝ[X],
    muF a b i (nb a b i j * g) = muF a b (i + j) (g.comp (X + C (pt a b i j))) := by
  intro j
  induction j with
  | zero => intro i _ g; simp [nb, pt]
  | succ j ih =>
    intro i hij g
    rw [nb_succ, mul_assoc, muF_X_mul (by omega), mul_comp, comp_shift_cancel,
      ih (i + 1) (by omega), show i + 1 + j = i + (j + 1) by ring, comp_assoc]
    congr 2
    simp only [add_comp, X_comp, C_comp, pt_succ, kk, map_add]
    ring

lemma muF_X (hba : b < a) {i : ℕ} (h : i + 1 < P a b) : muF a b i X = 1 := by
  rw [← mul_one (X : ℝ[X]), muF_X_mul h, one_comp, muF_one hba (by omega)]

lemma muF_X_sq (hba : b < a) {i : ℕ} (h : i + 2 < P a b) : muF a b i (X ^ 2) = kk a b i + 1 := by
  rw [sq, muF_X_mul (by omega), X_comp, muF_add, muF_X hba (by omega), muF_C,
    muF_one hba (by omega)]
  ring

lemma muF_X_cube (hba : b < a) {i : ℕ} (h : i + 3 < P a b) :
    muF a b i (X ^ 3) = kk a b i ^ 2 + 2 * kk a b i + kk a b (i + 1) + 1 := by
  rw [show (X : ℝ[X]) ^ 3 = X * X ^ 2 by ring, muF_X_mul (by omega), pow_comp, X_comp,
    show (X + C (kk a b i)) ^ 2 = X ^ 2 + C (2 * kk a b i) * X + C (kk a b i ^ 2) by
      simp only [map_mul, map_pow, map_ofNat]; ring,
    muF_add, muF_add, muF_C_mul, muF_C, muF_X_sq hba (by omega), muF_X hba (by omega),
    muF_one hba (by omega)]
  ring

end Basic

section Positivity

lemma nuF_sq_nonneg (hba : b < a) {i : ℕ} (hi : i < P a b) (f : ℝ[X]) :
    0 ≤ nuF a b i (f * f) := by
  have hw := (wt_spec hba (P a b - 1 - i) i (by omega)).1
  unfold nuF
  refine sum_nonneg fun j hj => ?_
  have hj' := mem_range.mp hj
  have h1 := hw j hj'
  have h2 : (0 : ℝ) < qq a b (i + j) := by exact_mod_cast qq_pos hba (by omega)
  rw [eval_mul]
  exact div_nonneg (mul_nonneg h1.le (mul_self_nonneg _)) h2.le

/-- `νᵢ(f²) ≤ μᵢ(f²)/qᵢ`. -/
lemma nuF_sq_le (hba : b < a) {i : ℕ} (hi : i < P a b) (f : ℝ[X]) :
    nuF a b i (f * f) ≤ muF a b i (f * f) / qq a b i := by
  obtain ⟨hw, -⟩ := wt_spec hba (P a b - 1 - i) i (by omega)
  have hq0 : (0 : ℝ) < qq a b i := by exact_mod_cast qq_pos hba hi
  unfold nuF muF
  rw [sum_div]
  refine sum_le_sum fun j hj => ?_
  have hj' := mem_range.mp hj
  have hle : (qq a b i : ℝ) ≤ qq a b (i + j) := by exact_mod_cast qq_le_of_le (by omega) (by omega)
  have hnn : 0 ≤ wt a b i j * (f * f).eval (pt a b i j) := by
    rw [eval_mul]; exact mul_nonneg (hw j hj').le (mul_self_nonneg _)
  exact div_le_div_of_nonneg_left hnn hq0 hle

end Positivity

end PierceLengthBound
