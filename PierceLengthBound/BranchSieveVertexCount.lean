/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveCompletion
public import PierceLengthBound.HypersurfacePatternCountZero
public import Mathlib.Analysis.PSeries

/-! Transferring a square-root saving for four vertex labels to a count of
complete minor-chart patterns. A bound `C R^(7/2)` for bad first vertices in
every scaled box gives the bound `K C X^(9/2) (log₂ X + 1)` for chart states:
the completion count is summed over the common divisor `g`, with weight
`g^(-3/2)`, and then over dyadic bands of `m`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open scoped Matrix
noncomputable section
open Finset

open Classical in
/-- A bound for bad vertices in the box of side `X / g`, after scaling by `g`,
bounds the bad vertices of the box of side `X` all of whose coordinates are
divisible by `g`. -/
theorem branch_divisible_vertex_count (bad : (Fin 4 → ℤ) → Prop)
    {C : ℝ} (hC : 0 ≤ C) {g X : ℕ} (hg : 0 < g)
    (hbad : (((ibox4 (X / g)).filter fun x => bad (fun i => (g : ℤ) * x i)).card : ℝ) ≤
      C * (X / g : ℕ) ^ (7 / 2 : ℝ)) :
    (((ibox4 X).filter fun x => (∀ i, (g : ℤ) ∣ x i) ∧ bad x).card : ℝ) ≤
      C * ((X : ℝ) / g) ^ (7 / 2 : ℝ) := by
  classical
  let Z := (ibox4 (X / g)).filter fun x => bad (fun i => (g : ℤ) * x i)
  have hc : (((ibox4 X).filter fun x => (∀ i, (g : ℤ) ∣ x i) ∧ bad x).card : ℝ) ≤ Z.card := by
    exact_mod_cast card_le_card_of_injOn (fun x : Fin 4 → ℤ => fun i => x i / (g : ℤ))
      (t := Z) (fun x hx => by
        obtain ⟨hxbox, hd, hbadx⟩ := mem_filter.mp hx
        refine mem_filter.mpr ⟨ediv_mem_ibox4 hg hxbox hd, ?_⟩
        convert hbadx using 1
        funext i
        exact Int.mul_ediv_cancel' (hd i))
      (fun x hx y hy he => by
        have hdx := (mem_filter.mp hx).2.1
        have hdy := (mem_filter.mp hy).2.1
        funext i
        have hi : x i / (g : ℤ) = y i / (g : ℤ) := congrFun he i
        calc x i = (g : ℤ) * (x i / (g : ℤ)) := (Int.mul_ediv_cancel' (hdx i)).symm
          _ = (g : ℤ) * (y i / (g : ℤ)) := by rw [hi]
          _ = y i := Int.mul_ediv_cancel' (hdy i))
  apply (hc.trans hbad).trans
  gcongr
  exact Nat.cast_div_le

/-- A minor-chart state `(m, u, v)`: the pivot, the first-vertex coordinates and
the second vector. -/
def BranchChartState := ℕ × (Fin 3 → ℤ) × (Fin 3 → ℤ)

open Classical in
/-- One common-factor class, in a band `M ≤ m ≤ 2M`, has a uniform completion bound. -/
theorem branch_vertex_band_gcd_count (bad : (Fin 4 → ℤ) → Prop)
    {C : ℝ} (_hC : 0 ≤ C) {X M g : ℕ} (hM : 0 < M) (hg : 0 < g)
    (S : Finset BranchChartState)
    (hS : ∀ w ∈ S, M ≤ w.1 ∧ w.1 ≤ 2 * M ∧ w.1 ≤ X ∧
      w.2.1 ∈ ibox3 w.1 ∧ w.2.2 ∈ ibox3 X ∧
      (∀ j, (w.1 : ℤ) ∣ (w.2.1 ⨯₃ w.2.2) j) ∧
      bad (integerFirstVertex w.1 w.2.1) ∧ gcd4 w.1 w.2.1 = g)
    (hbad : (((ibox4 (2 * M)).filter fun x =>
      (∀ i, (g : ℤ) ∣ x i) ∧ bad x).card : ℝ) ≤
        C * ((2 * M : ℝ) / g) ^ (7 / 2 : ℝ)) :
    (S.card : ℝ) ≤ C * ((2 * M : ℝ) / g) ^ (7 / 2 : ℝ) *
      (729 * (X : ℝ) ^ 3 * (g : ℝ) ^ 2 / (M : ℝ) ^ 2) := by
  classical
  let V := (ibox4 (2 * M)).filter fun x => (∀ i, (g : ℤ) ∣ x i) ∧ bad x
  let key (w : BranchChartState) := integerFirstVertex w.1 w.2.1
  have hmaps : ∀ w ∈ S, key w ∈ V := by
    intro w hw
    obtain ⟨hlo, hhi, hX, hu, hv, hcross, hbadw, hgw⟩ := hS w hw
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => ?_), ?_, hbadw⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · change (w.1 : ℤ) ∈ Icc (-((2 * M : ℕ) : ℤ)) (2 * M : ℕ)
        exact mem_Icc.mpr ⟨by omega, by exact_mod_cast hhi⟩
      · have hj := mem_Icc.mp (Fintype.mem_piFinset.mp hu j)
        change w.2.1 j ∈ Icc (-((2 * M : ℕ) : ℤ)) (2 * M : ℕ)
        apply mem_Icc.mpr
        have hh : (w.1 : ℤ) ≤ (2 * M : ℕ) := by exact_mod_cast hhi
        omega
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change (g : ℤ) ∣ (w.1 : ℤ)
        rw [← hgw]
        exact_mod_cast gcd4_dvd_m w.1 w.2.1
      · change (g : ℤ) ∣ w.2.1 j
        rw [← hgw]
        exact gcd4_dvd w.1 w.2.1 j
  have hfiber : ∀ x ∈ V, ((S.filter fun w => key w = x).card : ℝ) ≤
      729 * (X : ℝ) ^ 3 * (g : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
    intro x _
    by_cases hne : (S.filter fun w => key w = x).Nonempty
    · obtain ⟨w0, hw0⟩ := hne
      obtain ⟨hw0S, hw0x⟩ := mem_filter.mp hw0
      obtain ⟨hlo, hhi, hX, hu, hv, hcross, hbadw, hgw⟩ := hS w0 hw0S
      have hmpos : 0 < w0.1 := hM.trans_le hlo
      have hcoords w (hw : w ∈ S.filter fun w => key w = x) :
          w.1 = w0.1 ∧ w.2.1 = w0.2.1 :=
        integerFirstVertex_injective ((mem_filter.mp hw).2.trans hw0x.symm)
      have hi : (S.filter fun w => key w = x).card ≤
          ((ibox3 X).filter fun v => ∀ j, (w0.1 : ℤ) ∣ (w0.2.1 ⨯₃ v) j).card := by
        apply card_le_card_of_injOn (fun w => w.2.2)
        · intro w hw
          obtain ⟨hwm, hwu⟩ := hcoords w hw
          have hh := hS w (mem_filter.mp hw).1
          refine mem_filter.mpr ⟨hh.2.2.2.2.1, ?_⟩
          simpa only [hwm, hwu] using hh.2.2.2.2.2.1
        · intro w hw w' hw' he
          have hc := hcoords w hw
          have hc' := hcoords w' hw'
          exact Prod.ext (hc.1.trans hc'.1.symm) (Prod.ext (hc.2.trans hc'.2.symm) he)
      calc
        _ ≤ (((ibox3 X).filter fun v => ∀ j, (w0.1 : ℤ) ∣ (w0.2.1 ⨯₃ v) j).card : ℝ) := by
          exact_mod_cast hi
        _ ≤ 729 * (X : ℝ) ^ 3 * (g : ℝ) ^ 2 / (w0.1 : ℝ) ^ 2 := by
          simpa only [hgw] using branch_completion_count hmpos hX w0.2.1
        _ ≤ _ := by
          gcongr
    · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
      positivity
  have hc : (S.card : ℝ) ≤ (V.card : ℝ) *
      (729 * (X : ℝ) ^ 3 * (g : ℝ) ^ 2 / (M : ℝ) ^ 2) := by
    rw [card_eq_sum_card_fiberwise (f := key) (t := V) hmaps, Nat.cast_sum]
    calc
      _ ≤ ∑ _x ∈ V, (729 * (X : ℝ) ^ 3 * (g : ℝ) ^ 2 / (M : ℝ) ^ 2) :=
        sum_le_sum hfiber
      _ = _ := by simp
  exact hc.trans (mul_le_mul_of_nonneg_right hbad (by positivity))

lemma branch_vertex_weight_identity {M g : ℝ} (hM : 0 < M) (hg : 0 < g) :
    ((2 * M) / g) ^ (7 / 2 : ℝ) * (g ^ 2 / M ^ 2) =
      (2 : ℝ) ^ (7 / 2 : ℝ) * M ^ (3 / 2 : ℝ) * g ^ (-3 / 2 : ℝ) := by
  have hpowM : M ^ (3 / 2 : ℝ) = M ^ (7 / 2 : ℝ) / M ^ 2 := by
    rw [show (3 / 2 : ℝ) = 7 / 2 - 2 by norm_num, Real.rpow_sub hM]
    norm_num
  have hpowg : g ^ (-3 / 2 : ℝ) = g ^ 2 / g ^ (7 / 2 : ℝ) := by
    rw [show (-3 / 2 : ℝ) = 2 - 7 / 2 by norm_num, Real.rpow_sub hg]
    norm_num
  rw [Real.div_rpow (by positivity) hg.le, Real.mul_rpow (by norm_num) hM.le,
    hpowM, hpowg]
  ring

open Classical in
/-- A universal constant bounds the sum over all possible common divisors. -/
theorem branch_vertex_band_count :
    ∃ K : ℝ, 0 < K ∧ ∀ (bad : (Fin 4 → ℤ) → Prop) (C : ℝ), 0 ≤ C →
      ∀ X M : ℕ, 0 < M → M ≤ X → ∀ S : Finset BranchChartState,
      (∀ w ∈ S, M ≤ w.1 ∧ w.1 ≤ 2 * M ∧ w.1 ≤ X ∧
        w.2.1 ∈ ibox3 w.1 ∧ w.2.2 ∈ ibox3 X ∧
        (∀ j, (w.1 : ℤ) ∣ (w.2.1 ⨯₃ w.2.2) j) ∧
        bad (integerFirstVertex w.1 w.2.1)) →
      (∀ g ∈ Icc 1 (2 * M),
        (((ibox4 (2 * M / g)).filter fun x => bad (fun i => (g : ℤ) * x i)).card : ℝ) ≤
          C * (2 * M / g : ℕ) ^ (7 / 2 : ℝ)) →
      (S.card : ℝ) ≤ K * C * (X : ℝ) ^ (9 / 2 : ℝ) := by
  let Z : ℝ := ∑' g : ℕ, (g : ℝ) ^ (-3 / 2 : ℝ)
  have hZ : 0 ≤ Z := tsum_nonneg fun g => Real.rpow_nonneg (Nat.cast_nonneg g) _
  have hsum : Summable (fun g : ℕ => (g : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  let K₀ : ℝ := 729 * (2 : ℝ) ^ (7 / 2 : ℝ) * Z
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  refine ⟨K₀ + 1, by positivity, ?_⟩
  intro bad C hC X M hM hMX S hS hbad
  let gcdkey (w : BranchChartState) := gcd4 w.1 w.2.1
  have hmaps : ∀ w ∈ S, gcdkey w ∈ Icc 1 (2 * M) := by
    intro w hw
    have hh := hS w hw
    have hmpos : 0 < w.1 := hM.trans_le hh.1
    exact mem_Icc.mpr ⟨gcd4_pos hmpos _,
      (Nat.le_of_dvd hmpos (gcd4_dvd_m w.1 w.2.1)).trans hh.2.1⟩
  have hgcount : ∀ g ∈ Icc 1 (2 * M),
      ((S.filter fun w => gcdkey w = g).card : ℝ) ≤
        (729 * (2 : ℝ) ^ (7 / 2 : ℝ) * C * (X : ℝ) ^ 3 * (M : ℝ) ^ (3 / 2 : ℝ)) *
          (g : ℝ) ^ (-3 / 2 : ℝ) := by
    intro g hg
    have hgpos : 0 < g := (mem_Icc.mp hg).1
    have hv := branch_divisible_vertex_count bad hC hgpos (hbad g hg)
    have hc := branch_vertex_band_gcd_count bad hC hM hgpos
      (S.filter fun w => gcdkey w = g) (fun w hw => by
        obtain ⟨hw, he⟩ := mem_filter.mp hw
        obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := hS w hw
        exact ⟨h1,h2,h3,h4,h5,h6,h7,he⟩) (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hv)
    apply hc.trans_eq
    have he := branch_vertex_weight_identity
      (show (0 : ℝ) < M by exact_mod_cast hM)
      (show (0 : ℝ) < g by exact_mod_cast hgpos)
    calc
      _ = (729 * C * (X : ℝ) ^ 3) *
          (((2 * (M : ℝ)) / g) ^ (7 / 2 : ℝ) * ((g : ℝ) ^ 2 / (M : ℝ) ^ 2)) := by ring
      _ = _ := by rw [he]; ring
  have hc : (S.card : ℝ) ≤ K₀ * C * (X : ℝ) ^ 3 * (M : ℝ) ^ (3 / 2 : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := gcdkey) (t := Icc 1 (2 * M)) hmaps, Nat.cast_sum]
    calc
      _ ≤ ∑ g ∈ Icc 1 (2 * M),
          (729 * (2 : ℝ) ^ (7 / 2 : ℝ) * C * (X : ℝ) ^ 3 * (M : ℝ) ^ (3 / 2 : ℝ)) *
            (g : ℝ) ^ (-3 / 2 : ℝ) := sum_le_sum hgcount
      _ = (729 * (2 : ℝ) ^ (7 / 2 : ℝ) * C * (X : ℝ) ^ 3 * (M : ℝ) ^ (3 / 2 : ℝ)) *
          ∑ g ∈ Icc 1 (2 * M), (g : ℝ) ^ (-3 / 2 : ℝ) := by rw [mul_sum]
      _ ≤ (729 * (2 : ℝ) ^ (7 / 2 : ℝ) * C * (X : ℝ) ^ 3 * (M : ℝ) ^ (3 / 2 : ℝ)) * Z := by
        apply mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun _ _ => by positivity))
        positivity
      _ = _ := by dsimp [K₀]; ring
  calc
    _ ≤ K₀ * C * (X : ℝ) ^ 3 * (X : ℝ) ^ (3 / 2 : ℝ) := hc.trans (by gcongr)
    _ = K₀ * C * (X : ℝ) ^ (9 / 2 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add (show (0 : ℝ) < X by
        exact_mod_cast hM.trans_le hMX)]
      norm_num
    _ ≤ _ := by gcongr; linarith

open Classical in
/-- Dyadic bands retain the square-root saving, at a logarithmic cost. -/
theorem branch_chart_bad_count :
    ∃ K : ℝ, 0 < K ∧ ∀ (bad : (Fin 4 → ℤ) → Prop) (C : ℝ), 0 ≤ C →
      ∀ X : ℕ, 0 < X → ∀ S : Finset BranchChartState,
      (∀ w ∈ S, 0 < w.1 ∧ w.1 ≤ X ∧
        w.2.1 ∈ ibox3 w.1 ∧ w.2.2 ∈ ibox3 X ∧
        (∀ j, (w.1 : ℤ) ∣ (w.2.1 ⨯₃ w.2.2) j) ∧
        bad (integerFirstVertex w.1 w.2.1)) →
      (∀ g R : ℕ, 0 < g → g ≤ 2 * X → 0 < R → R ≤ 2 * X →
        (((ibox4 R).filter fun x => bad (fun i => (g : ℤ) * x i)).card : ℝ) ≤
          C * (R : ℝ) ^ (7 / 2 : ℝ)) →
      (S.card : ℝ) ≤ K * C * (X : ℝ) ^ (9 / 2 : ℝ) * (Nat.log 2 X + 1 : ℕ) := by
  obtain ⟨K, hK, hband⟩ := branch_vertex_band_count
  refine ⟨K, hK, ?_⟩
  intro bad C hC X hX S hS hbad
  have hmaps : ∀ w ∈ S, Nat.log 2 w.1 ∈ range (Nat.log 2 X + 1) := by
    intro w hw
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hS w hw).2.1))
  have hkcount : ∀ k ∈ range (Nat.log 2 X + 1),
      ((S.filter fun w => Nat.log 2 w.1 = k).card : ℝ) ≤
        K * C * (X : ℝ) ^ (9 / 2 : ℝ) := by
    intro k hk
    have hMX : 2 ^ k ≤ X := Nat.pow_le_of_le_log hX.ne' (by simpa using hk)
    apply hband bad C hC X (2 ^ k) (by positivity) hMX
    · intro w hw
      obtain ⟨hw, he⟩ := mem_filter.mp hw
      obtain ⟨hm, hmX, hu, hv, hcross, hbadw⟩ := hS w hw
      have hlo := Nat.pow_log_le_self 2 hm.ne'
      have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) w.1
      rw [he] at hlo hhi
      rw [pow_succ] at hhi
      exact ⟨hlo, by omega, hmX, hu, hv, hcross, hbadw⟩
    · intro g hg
      have hgpos : 0 < g := (mem_Icc.mp hg).1
      have hgM := (mem_Icc.mp hg).2
      exact hbad g (2 * 2 ^ k / g) hgpos
        (hgM.trans (Nat.mul_le_mul_left 2 hMX))
        (Nat.div_pos hgM hgpos)
        ((Nat.div_le_self _ _).trans (Nat.mul_le_mul_left 2 hMX))
  rw [card_eq_sum_card_fiberwise (f := fun w : BranchChartState => Nat.log 2 w.1)
    (t := range (Nat.log 2 X + 1)) hmaps, Nat.cast_sum]
  calc
    _ ≤ ∑ _k ∈ range (Nat.log 2 X + 1), K * C * (X : ℝ) ^ (9 / 2 : ℝ) :=
      sum_le_sum hkcount
    _ = _ := by simp [mul_comm]

end
end PierceLengthBound.FixedDividend
