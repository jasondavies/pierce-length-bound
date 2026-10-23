/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftExponent
public import PierceLengthBound.Gram

/-! The added coordinate is a positive integer with the required small box bound
at actual selected orbit starts. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset Polynomial Matrix

/-- The integral rank-three Hankel invariant, written in actual drops and gaps. -/
def integralLiftCoordinate (a b i : ℕ) : ℤ :=
  dq a b i * kq a b (i + 1) - dq a b (i + 1) * kq a b i

lemma integralLiftCoordinate_eq {a b i : ℕ} (hba : b < a) (hi : i + 3 < P a b) :
    (integralLiftCoordinate a b i : ℝ) = hankelInv a b i 3 := by
  rw [hankelInv_three hba hi]
  simp [integralLiftCoordinate, dq, kq, kv]

lemma integralLiftCoordinate_pos {a b i : ℕ} (hba : b < a) (hi : i + 3 < P a b) :
    1 ≤ integralLiftCoordinate a b i := by
  have h := hankelInv_pos hba (i := i) (r := 3) (by omega) (by omega)
  rw [← integralLiftCoordinate_eq hba hi] at h
  have : (0 : ℤ) < integralLiftCoordinate a b i := by exact_mod_cast h
  omega

/-- Rank-three Newton Gram product, retaining the exact lower-degree terms. -/
def gramThree (k0 k1 k2 : ℤ) : ℤ :=
  (k0 + 1) * ((k0 + k1) * k1 + k0 + 2 * k1 + k2 + 1)

lemma muF_nb_sq_three {a b i : ℕ} (hba : b < a) (hi : i + 4 < P a b) :
    ∏ j : Fin 3, muF a b i (nb a b i j * nb a b i j) =
      (gramThree (kq a b i) (kq a b (i + 1)) (kq a b (i + 2)) : ℝ) := by
  have p1 : pt a b i 1 = kk a b i := by rw [pt_eq_sum]; simp
  have p2 : pt a b i 2 = kk a b i + kk a b (i + 1) := by
    rw [pt_eq_sum]; simp [sum_range_succ]
  have e : ∀ j : ℕ, j < 3 → muF a b i (nb a b i j * nb a b i j) =
      muF a b (i + j) ((nb a b i j).comp (X + C (pt a b i j))) :=
    fun j hj => muF_nb_mul j i (by omega) _
  rw [Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
  simp only [nb, prod_range_succ, prod_range_zero, one_mul, mul_comp, sub_comp, X_comp,
    C_comp, one_comp, pt_zero, map_zero, sub_zero, add_zero]
  rw [muF_one hba (by omega), p1, p2]
  rw [show (X + C (kk a b i)) = X + C (kk a b i) * 1 by ring, muF_add, muF_C_mul,
    muF_X hba (by omega), muF_one hba (by omega)]
  have he : (X + C (kk a b i + kk a b (i + 1))) *
      (X + C (kk a b i + kk a b (i + 1)) - C (kk a b i)) =
      X ^ 2 + C (2 * kk a b (i + 1) + kk a b i) * X +
        C ((kk a b i + kk a b (i + 1)) * kk a b (i + 1)) * 1 := by
    simp only [map_add, map_mul, map_ofNat]
    ring
  rw [he]
  simp only [muF_add, muF_C_mul]
  rw [muF_X_sq hba (by omega), muF_X hba (by omega), muF_one hba (by omega)]
  simp only [gramThree, kq, kk, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  ring

lemma gramThree_le {k0 k1 k2 H : ℤ} (hH : 1 ≤ H)
    (h0 : 0 ≤ k0) (h1 : 0 ≤ k1) (h2 : 0 ≤ k2)
    (hb0 : k0 ≤ H) (hb1 : k1 ≤ H) (hb2 : k2 ≤ H) : gramThree k0 k1 k2 ≤ 14 * H ^ 3 := by
  have hp : (k0 + k1) * k1 ≤ 2 * H ^ 2 := by
    calc _ ≤ (H + H) * H := by gcongr
      _ = _ := by ring
  have ht : (k0 + k1) * k1 + k0 + 2 * k1 + k2 + 1 ≤ 7 * H ^ 2 := by
    nlinarith [sq_nonneg (H - 1)]
  calc
    gramThree k0 k1 k2 ≤ (2 * H) * (7 * H ^ 2) := by
      unfold gramThree
      apply mul_le_mul (by omega) ht (by positivity) (by positivity)
    _ = _ := by ring

/-- The actual positive integer invariant satisfies a cubic Gram height bound. -/
theorem integralLiftCoordinate_height {a b i H : ℕ} (hba : b < a) (hi : i + 4 < P a b)
    (hH : 1 ≤ H) (hk : ∀ j < 3, kq a b (i + j) ≤ H) :
    integralLiftCoordinate a b i * (qq a b i : ℤ) ^ 3 ≤ 14 * (a : ℤ) * H ^ 3 := by
  have h := hankelInv_le_prod hba (i := i) (r := 3) (by omega) (by omega)
  rw [← integralLiftCoordinate_eq hba (by omega), prod_div_distrib, muF_nb_sq_three hba hi] at h
  simp only [prod_const, card_univ, Fintype.card_fin] at h
  have hq : (0 : ℝ) < (qq a b i : ℝ) ^ 3 := by
    have : (0 : ℝ) < qq a b i := by exact_mod_cast qq_pos hba (by omega)
    positivity
  rw [mul_div_assoc', le_div_iff₀ hq] at h
  have h' : integralLiftCoordinate a b i * (qq a b i : ℤ) ^ 3 ≤
      (a : ℤ) * gramThree (kq a b i) (kq a b (i + 1)) (kq a b (i + 2)) := by exact_mod_cast h
  have hb := gramThree_le (by exact_mod_cast hH)
    (show 0 ≤ kq a b i by have := kq_pos (a := a) (b := b) (i := i) (by omega); omega)
    (show 0 ≤ kq a b (i + 1) by have := kq_pos (a := a) (b := b) (i := i + 1) (by omega); omega)
    (show 0 ≤ kq a b (i + 2) by have := kq_pos (a := a) (b := b) (i := i + 2) (by omega); omega)
    (by simpa using hk 0 (by decide)) (hk 1 (by decide)) (hk 2 (by decide))
  calc _ ≤ (a : ℤ) * gramThree (kq a b i) (kq a b (i + 1)) (kq a b (i + 2)) := h'
    _ ≤ (a : ℤ) * (14 * (H : ℤ) ^ 3) := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg a)
    _ = _ := by ring

/-- Every selected state lifts to a positive integer in the exact, unrounded box
used by the new local count. -/
theorem selected_integralLiftCoordinate_bound {a b s T A i : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A) :
    1 ≤ integralLiftCoordinate a b i ∧
      integralLiftCoordinate a b i ≤ (selectedLiftHeight a A T : ℕ) := by
  obtain ⟨hP, hk, hA⟩ := selectedStart_spec hmem hsT hi
  have hp := integralLiftCoordinate_pos hba (by omega : i + 3 < P a b)
  refine ⟨hp, ?_⟩
  have hh := integralLiftCoordinate_height hba (by omega : i + 4 < P a b)
    (show 1 ≤ selectedGapHeight a A T from Nat.le_add_left 1 _)
    (fun j hj => (hk j (by omega)).2)
  have hq := window_quotient_lower hba (by omega : i < P a b) hA
  have hqZ : (a : ℤ) ≤ 4 * A * qq a b i := by exact_mod_cast hq
  have hb : integralLiftCoordinate a b i * (a : ℤ) ^ 3 ≤
      896 * (a : ℤ) * A ^ 3 * (selectedGapHeight a A T : ℤ) ^ 3 := by
    calc _ ≤ integralLiftCoordinate a b i * (4 * (A : ℤ) * qq a b i) ^ 3 := by gcongr
      _ = (64 * (A : ℤ) ^ 3) * (integralLiftCoordinate a b i * (qq a b i : ℤ) ^ 3) := by ring
      _ ≤ (64 * (A : ℤ) ^ 3) * (14 * (a : ℤ) * (selectedGapHeight a A T : ℤ) ^ 3) := by gcongr
      _ = _ := by ring
  have ha : (0 : ℤ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb' : integralLiftCoordinate a b i * (a : ℤ) ^ 2 ≤
      896 * (A : ℤ) ^ 3 * (selectedGapHeight a A T : ℤ) ^ 3 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    convert hb using 1 <;> ring
  have hd := Int.le_ediv_of_mul_le (by positivity : (0 : ℤ) < (a : ℤ) ^ 2) hb'
  simpa only [selectedLiftHeight, Int.natCast_div, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    using hd

end
end PierceLengthBound.FixedDividend
