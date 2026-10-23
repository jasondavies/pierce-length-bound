/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftRawResolvent
public import PierceLengthBound.JointLiftExponent
public import PierceLengthBound.JointLiftAlgebra
public import PierceLengthBound.FixedDividendWindow

/-! The rank-five integer coordinate lies in the joint-lift box at actual selected states. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset Polynomial

/-- Positive moments preserve inequalities on their actual finite support. -/
lemma muF_mono_on_support {a b i : ℕ} (hba : b < a) (hi : i < P a b)
    {f g : ℝ[X]} (hfg : ∀ t < P a b - i, f.eval (pt a b i t) ≤ g.eval (pt a b i t)) :
    muF a b i f ≤ muF a b i g := by
  have hw := (wt_spec hba (P a b - 1 - i) i (by omega)).1
  exact sum_le_sum fun t ht => mul_le_mul_of_nonneg_left
    (hfg t (mem_range.mp ht)) (hw t (mem_range.mp ht)).le

/-- A Newton square is controlled by a shifted ordinary moment. -/
lemma newton_square_le_shift {a b i j : ℕ} (hba : b < a) (hij : i + j < P a b)
    {H : ℝ} (hk : ∀ t < j, kk a b (i + t) ≤ H) :
    muF a b i (nb a b i j * nb a b i j) ≤
      muF a b (i + j) ((X + C (j * H)) ^ j) := by
  rw [muF_nb_mul j i hij]
  apply muF_mono_on_support hba hij
  intro t ht
  have hx : 0 ≤ pt a b (i + j) t := by
    have := pt_ge (a := a) (b := b) (i := i + j) (j := t) (by omega)
    exact le_trans (Nat.cast_nonneg t) this
  have hp : pt a b i j ≤ j * H := by
    rw [pt_eq_sum]
    calc (∑ m ∈ range j, kk a b (i + m)) ≤ ∑ _m ∈ range j, H :=
          sum_le_sum fun m hm => hk m (mem_range.mp hm)
      _ = _ := by simp
  have hpl (l : ℕ) (hl : l < j) : 0 ≤ pt a b i l ∧ pt a b i l ≤ pt a b i j := by
    have hq := qq_le_of_le (a := a) (b := b) (show i + l ≤ i + j by omega) hij
    have hqR : (qq a b (i + l) : ℝ) ≤ qq a b (i + j) := by exact_mod_cast hq
    have h0 := pt_ge (a := a) (b := b) (i := i) (j := l) (by omega)
    exact ⟨(Nat.cast_nonneg l).trans h0, by simp only [pt]; linarith⟩
  simp only [eval_comp, eval_add, eval_X, eval_C, eval_pow, nb, eval_prod, eval_sub]
  calc (∏ l ∈ range j, (pt a b (i + j) t + pt a b i j - pt a b i l)) ≤
      ∏ _l ∈ range j, (pt a b (i + j) t + j * H) := by
        apply prod_le_prod₀
        · intro l hl
          have := (hpl l (mem_range.mp hl)).2
          linarith
        · intro l hl
          have := (hpl l (mem_range.mp hl)).1
          linarith
    _ = _ := by simp

/-- The five explicit bounds used in the rank-five Newton Gram product. -/
def rankFiveMomentConstant : Fin 5 → ℝ := ![1, 2, 10, 77, 799]

lemma rankFive_shift_moment_bound {a b i : ℕ} (hba : b < a) (hi : i + 8 < P a b)
    {H : ℝ} (hH : 1 ≤ H) (hk : ∀ t < 7, 0 ≤ kk a b (i + t) ∧ kk a b (i + t) ≤ H)
    (j : Fin 5) :
    muF a b (i + j) ((X + C (j.val * H)) ^ j.val) ≤ rankFiveMomentConstant j * H ^ j.val := by
  have hH0 : 0 ≤ H := by linarith
  have hpow (r s : ℕ) (hrs : r ≤ s) : H ^ r ≤ H ^ s := pow_le_pow_right₀ hH hrs
  have hkn (t : ℕ) (ht : t < 7) := (hk t ht).1
  have hkb (t : ℕ) (ht : t < 7) := (hk t ht).2
  fin_cases j
  · simp [rankFiveMomentConstant, muF_one hba (by omega : i < P a b)]
  · have hb : muF a b (i + 1) (X + C H) ≤ 2 * H := by
      rw [muF_add, muF_C, muF_X hba (by omega), muF_one hba (by omega)]
      linarith
    convert hb using 1 <;> norm_num [rankFiveMomentConstant]
  · change muF a b (i + 2) ((X + C (2 * H)) ^ 2) ≤ 10 * H ^ 2
    rw [muF_shift_sq hba (by omega)]
    have h := hkb 2 (by omega)
    nlinarith [hpow 0 2 (by omega), hpow 1 2 (by omega)]
  · change muF a b (i + 3) ((X + C (3 * H)) ^ 3) ≤ 77 * H ^ 3
    rw [muF_shift_cube hba (by omega)]
    have h2 : kk a b (i + 3) ^ 2 ≤ H ^ 2 :=
      pow_le_pow_left₀ (hkn 3 (by omega)) (hkb 3 (by omega)) 2
    have h3 : 3 * H * (kk a b (i + 3) + 1) ≤ 3 * H * (H + 1) := by
      gcongr; exact hkb 3 (by omega)
    have h := hkb 3 (by omega)
    have h' := hkb 4 (by omega)
    nlinarith [hpow 0 3 (by omega), hpow 1 3 (by omega), hpow 2 3 (by omega)]
  · change muF a b (i + 4) ((X + C (4 * H)) ^ 4) ≤ 799 * H ^ 4
    rw [muF_shift_four hba (by omega)]
    have hk4 := hk 4 (by omega)
    have hk5 := hk 5 (by omega)
    have hk6 := hk 6 (by omega)
    have hb : (4 * H) ^ 4 + 4 * (4 * H) ^ 3 + 6 * (4 * H) ^ 2 * (kk a b (i + 4) + 1) +
        4 * (4 * H) * (kk a b (i + 4) ^ 2 + 2 * kk a b (i + 4) + kk a b (i + 4 + 1) + 1) +
        kk a b (i + 4) ^ 3 + 3 * kk a b (i + 4) ^ 2 +
        3 * kk a b (i + 4) * (kk a b (i + 4 + 1) + 1) +
        kk a b (i + 4 + 1) ^ 2 + 2 * kk a b (i + 4 + 1) + kk a b (i + 4 + 2) + 1 ≤
        (4 * H) ^ 4 + 4 * (4 * H) ^ 3 + 6 * (4 * H) ^ 2 * (H + 1) +
        4 * (4 * H) * (H ^ 2 + 2 * H + H + 1) + H ^ 3 + 3 * H ^ 2 +
        3 * H * (H + 1) + H ^ 2 + 2 * H + H + 1 := by
      simp only [Nat.add_assoc] at *
      gcongr <;> linarith
    apply hb.trans
    nlinarith [hpow 0 4 (by omega), hpow 1 4 (by omega),
      hpow 2 4 (by omega), hpow 3 4 (by omega)]

/-- Uniform rank-five Newton Gram product, with the candidate's explicit constant. -/
theorem rankFive_newton_product_bound {a b i : ℕ} (hba : b < a) (hi : i + 8 < P a b)
    {H : ℝ} (hH : 1 ≤ H) (hk : ∀ t < 7, 0 ≤ kk a b (i + t) ∧ kk a b (i + t) ≤ H) :
    (∏ j : Fin 5, muF a b i (nb a b i j * nb a b i j)) ≤ 1230460 * H ^ 10 := by
  have hd (j : Fin 5) : muF a b i (nb a b i j * nb a b i j) ≤
      rankFiveMomentConstant j * H ^ j.val := by
    have hj := j.isLt
    exact (newton_square_le_shift hba (by omega)
      (fun t ht => (hk t (by omega)).2)).trans (rankFive_shift_moment_bound hba hi hH hk j)
  have hn (j : Fin 5) : 0 ≤ muF a b i (nb a b i j * nb a b i j) := by
    have hw := (wt_spec hba (P a b - 1 - i) i (by omega)).1
    unfold muF
    refine sum_nonneg fun t ht => ?_
    rw [eval_mul]
    exact mul_nonneg (hw t (mem_range.mp ht)).le (mul_self_nonneg _)
  calc _ ≤ ∏ j : Fin 5, (rankFiveMomentConstant j * H ^ j.val) :=
          prod_le_prod₀ (fun j _ => hn j) (fun j _ => hd j)
    _ = _ := by
      simp [Fin.prod_univ_succ, rankFiveMomentConstant]
      ring

/-- The rank-five Hankel invariant has height O(a H^10 / q^5). -/
theorem rankFive_height {a b i H : ℕ} (hba : b < a) (hi : i + 8 < P a b)
    (hH : 1 ≤ H) (hk : ∀ t < 7, 1 ≤ kq a b (i + t) ∧ kq a b (i + t) ≤ H) :
    hankelInv a b i 5 * (qq a b i : ℝ) ^ 5 ≤ 1230460 * a * (H : ℝ) ^ 10 := by
  have hkr : ∀ t < 7, 0 ≤ kk a b (i + t) ∧ kk a b (i + t) ≤ (H : ℝ) := by
    intro t ht
    have he : kk a b (i + t) = (kq a b (i + t) : ℝ) := by simp [kk, kq]
    rw [he]
    exact ⟨by exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 1) (hk t ht).1),
      by exact_mod_cast (hk t ht).2⟩
  have h := hankelInv_le_prod hba (i := i) (r := 5) (by omega) (by omega)
  rw [prod_div_distrib] at h
  simp only [prod_const, card_univ, Fintype.card_fin] at h
  have hq : (0 : ℝ) < qq a b i := by exact_mod_cast qq_pos hba (by omega)
  rw [mul_div_assoc', le_div_iff₀ (pow_pos hq 5)] at h
  calc _ ≤ a * ∏ j : Fin 5, muF a b i (nb a b i j * nb a b i j) := h
    _ ≤ a * (1230460 * (H : ℝ) ^ 10) := by
      gcongr
      exact rankFive_newton_product_bound hba hi (by exact_mod_cast hH) hkr
    _ = _ := by ring

/-- The actual positive integer J=A D lies in the exact floored selected box. -/
theorem selected_rankFive_bound {a b s T A i J : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A)
    (hJ : (Lz a b i : ℝ) * orbitNorm a b i = J) :
    J ≤ selectedRankFiveHeight a A T := by
  obtain ⟨hP, hk, hA⟩ := selectedStart_spec hmem hsT hi
  have hh := rankFive_height hba hP
    (show 1 ≤ selectedGapHeight a A T from Nat.le_add_left 1 _) hk
  rw [← joint_rank_five_identity hba (by omega), hJ] at hh
  have hhN : J * qq a b i ^ 5 ≤ 1230460 * a * selectedGapHeight a A T ^ 10 := by
    exact_mod_cast hh
  have hq := window_quotient_lower hba (by omega : i < P a b) hA
  have hb : J * a ^ 5 ≤ 1259991040 * a * A ^ 5 * selectedGapHeight a A T ^ 10 := by
    calc _ ≤ J * (4 * A * qq a b i) ^ 5 := by gcongr
      _ = (1024 * A ^ 5) * (J * qq a b i ^ 5) := by ring
      _ ≤ (1024 * A ^ 5) * (1230460 * a * selectedGapHeight a A T ^ 10) := by gcongr
      _ = _ := by ring
  have ha : 0 < a := by omega
  have hb' : J * a ^ 4 ≤ 1259991040 * A ^ 5 * selectedGapHeight a A T ^ 10 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    convert hb using 1 <;> ring
  exact (Nat.le_div_iff_mul_le (by positivity : 0 < a ^ 4)).mpr hb'

/-- Positivity, integrality, and height hold simultaneously at every selected state. -/
theorem selected_rankFive_positive_integer {a b s T A i : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A) :
    ∃ J : ℕ, 0 < J ∧ (Lz a b i : ℝ) * orbitNorm a b i = J ∧
      J ≤ selectedRankFiveHeight a A T := by
  have hP := (selectedStart_spec hmem hsT hi).1
  obtain ⟨J, hpos, hJ⟩ := joint_rank_five_positive_integer hba (by omega : i + 7 < P a b)
  exact ⟨J, hpos, hJ, selected_rankFive_bound hba hmem hsT hi hJ⟩

end
end PierceLengthBound.FixedDividend
