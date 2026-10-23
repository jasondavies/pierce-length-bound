/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCountFirstVertices
public import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Counting the identically-zero polynomial fibers -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open scoped Matrix
noncomputable section
open MvPolynomial Finset

def zeroChartFibers (B : HypersurfaceChartPolynomial) (m : ℕ) :
    Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
  (crossSet m).filter fun uv => chartPolynomialFiber B (chartFirstVertex m uv.1) = 0

def integerFirstVertex (m : ℕ) (u : Fin 3 → ℤ) : Fin 4 → ℤ := Fin.cons (m : ℤ) u

lemma integerFirstVertex_injective {m n : ℕ} {u v : Fin 3 → ℤ}
    (h : integerFirstVertex m u = integerFirstVertex n v) : m = n ∧ u = v := by
  have h0 : (m : ℤ) = n := congrFun h 0
  refine ⟨by exact_mod_cast h0, ?_⟩
  funext i
  exact congrFun h i.succ

lemma integerFirstVertex_cast (m : ℕ) (u : Fin 3 → ℤ) :
    (fun i => (integerFirstVertex m u i : ℚ)) = chartFirstVertex m u := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · fin_cases j <;> rfl

/-- Each common-factor class of identically-zero fibers is controlled by the zero set of
one fixed nonzero coefficient of the chart polynomial. -/
theorem zeroChartFibers_gcd_count (B : HypersurfaceChartPolynomial)
    {q : MvPolynomial (Fin 4) ℚ} (hq : q ≠ 0)
    (hqzero : ∀ x, chartPolynomialFiber B x = 0 → eval x q = 0)
    {X g : ℕ} (hg : 0 < g) (hgX : g ≤ X) :
    ((((Icc 1 X).sigma fun m => zeroChartFibers B m).filter
      fun w => gcd4 w.1 w.2.1 = g).card : ℝ) ≤
      729 * q.totalDegree * (X : ℝ) ^ 4 / g := by
  classical
  let T := ((Icc 1 X).sigma fun m => zeroChartFibers B m).filter
    fun w => gcd4 w.1 w.2.1 = g
  let V := (ibox4 X).filter fun x => (∀ i, (g : ℤ) ∣ x i) ∧
    eval (fun i => (x i : ℚ)) q = 0
  let key := fun w : (m : ℕ) × ((Fin 3 → ℤ) × (Fin 3 → ℤ)) =>
    integerFirstVertex w.1 w.2.1
  have hmaps : ∀ w ∈ T, key w ∈ V := by
    intro w hw
    obtain ⟨hwT, hwg⟩ := mem_filter.mp hw
    obtain ⟨hm, huv⟩ := mem_sigma.mp hwT
    obtain ⟨huvcross, hfzero⟩ := mem_filter.mp huv
    have hu := (mem_product.mp (mem_filter.mp huvcross).1).1
    refine mem_filter.mpr ⟨?_, ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change (w.1 : ℤ) ∈ Icc (-(X : ℤ)) X
        exact mem_Icc.mpr ⟨by omega, by exact_mod_cast (mem_Icc.mp hm).2⟩
      · have hj := mem_Icc.mp (Fintype.mem_piFinset.mp hu j)
        change w.2.1 j ∈ Icc (-(X : ℤ)) X
        apply mem_Icc.mpr
        have hmX : (w.1 : ℤ) ≤ X := by exact_mod_cast (mem_Icc.mp hm).2
        omega
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change (g : ℤ) ∣ (w.1 : ℤ)
        rw [← hwg]
        exact_mod_cast gcd4_dvd_m w.1 w.2.1
      · change (g : ℤ) ∣ w.2.1 j
        rw [← hwg]
        exact gcd4_dvd w.1 w.2.1 j
    · change eval (fun i => (integerFirstVertex w.1 w.2.1 i : ℚ)) q = 0
      rw [integerFirstVertex_cast]
      exact hqzero _ hfzero
  have hcard : T.card ≤ V.card * (27 * X * g ^ 2) := by
    rw [mul_comm V.card]
    apply card_le_mul_card_image_of_maps_to (f := key) (t := V) hmaps (27 * X * g ^ 2)
    intro x _
    by_cases hne : (T.filter fun w => key w = x).Nonempty
    · obtain ⟨w0, hw0⟩ := hne
      obtain ⟨hw0T, hw0x⟩ := mem_filter.mp hw0
      obtain ⟨hw0S, hw0g⟩ := mem_filter.mp hw0T
      have hm0 := (mem_sigma.mp hw0S).1
      have hmpos : 0 < w0.1 := (mem_Icc.mp hm0).1
      have hcoords w (hw : w ∈ T.filter fun w => key w = x) :
          w.1 = w0.1 ∧ w.2.1 = w0.2.1 :=
        integerFirstVertex_injective ((mem_filter.mp hw).2.trans hw0x.symm)
      have hi : (T.filter fun w => key w = x).card ≤
          ((ibox3 w0.1).filter fun v => ∀ j, (w0.1 : ℤ) ∣ (w0.2.1 ⨯₃ v) j).card := by
        apply card_le_card_of_injOn (fun w => w.2.2)
        · intro w hw
          obtain ⟨hwm, hwu⟩ := hcoords w hw
          have huv := (mem_sigma.mp (mem_filter.mp (mem_filter.mp hw).1).1).2
          have hcross := mem_filter.mp (mem_filter.mp huv).1
          refine mem_filter.mpr ⟨?_, ?_⟩
          · simpa only [hwm] using (mem_product.mp hcross.1).2
          · simpa only [hwm, hwu] using hcross.2
        · intro w hw w' hw' he
          have hc := hcoords w hw
          have hc' := hcoords w' hw'
          exact Sigma.ext (hc.1.trans hc'.1.symm)
            (heq_of_eq (Prod.ext (hc.2.trans hc'.2.symm) he))
      refine hi.trans ((card_cross_fiber hmpos w0.2.1).trans ?_)
      rw [hw0g]
      gcongr
      exact (mem_Icc.mp hm0).2
    · rw [not_nonempty_iff_eq_empty.mp hne, card_empty]
      exact Nat.zero_le _
  have hv := polynomial_divisible_ibox4_count hq hg hgX
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hdiv : ((X / g : ℕ) : ℝ) ≤ (X : ℝ) / g := by
    exact Nat.cast_div_le
  calc (T.card : ℝ) ≤ (V.card : ℝ) * (27 * (X : ℝ) * g ^ 2) := by exact_mod_cast hcard
    _ ≤ (27 * q.totalDegree * (X / g : ℕ) ^ 3) * (27 * (X : ℝ) * g ^ 2) := by
      exact mul_le_mul_of_nonneg_right hv (by positivity)
    _ ≤ (27 * q.totalDegree * ((X : ℝ) / g) ^ 3) * (27 * (X : ℝ) * g ^ 2) := by gcongr
    _ = _ := by field_simp; ring

/-- A coarse harmonic estimate is enough: the identically-zero fibers are already below
the target exponent, without using the small epsilon loss. -/
theorem zeroChartFibers_sum (B : HypersurfaceChartPolynomial)
    {q : MvPolynomial (Fin 4) ℚ} (hq : q ≠ 0)
    (hqzero : ∀ x, chartPolynomialFiber B x = 0 → eval x q = 0)
    {X : ℕ} (hX : 1 ≤ X) :
    ∑ m ∈ Icc 1 X, ((zeroChartFibers B m).card : ℝ) ≤
      2187 * q.totalDegree * (X : ℝ) ^ (14 / 3 : ℝ) := by
  classical
  let T := (Icc 1 X).sigma fun m => zeroChartFibers B m
  have hXR : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hcard : (T.card : ℝ) = ∑ g ∈ Icc 1 X,
      ((T.filter fun w => gcd4 w.1 w.2.1 = g).card : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := fun w => gcd4 w.1 w.2.1) (t := Icc 1 X)
      (fun w hw => ?_), Nat.cast_sum]
    have hm := (mem_sigma.mp hw).1
    have hmpos : 0 < w.1 := (mem_Icc.mp hm).1
    exact mem_Icc.mpr ⟨gcd4_pos hmpos _,
      (Nat.le_of_dvd hmpos (gcd4_dvd_m w.1 w.2.1)).trans (mem_Icc.mp hm).2⟩
  have hharm : ∑ g ∈ Icc 1 X, (g : ℝ)⁻¹ ≤ 3 * (X : ℝ) ^ (2 / 3 : ℝ) := by
    have hh := harmonic_le_one_add_log X
    rw [harmonic_eq_sum_Icc] at hh
    push_cast at hh
    have hl := Real.log_natCast_le_rpow_div X (show (0 : ℝ) < 2 / 3 by norm_num)
    have hpow := Real.one_le_rpow (show (1 : ℝ) ≤ X by exact_mod_cast hX)
      (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    linarith
  have hsum : (T.card : ℝ) ≤ 729 * q.totalDegree * (X : ℝ) ^ 4 *
      ∑ g ∈ Icc 1 X, (g : ℝ)⁻¹ := by
    rw [hcard, mul_sum]
    apply sum_le_sum
    intro g hg
    convert zeroChartFibers_gcd_count B hq hqzero (mem_Icc.mp hg).1 (mem_Icc.mp hg).2 using 1
    ring
  have he : (X : ℝ) ^ 4 * (X : ℝ) ^ (2 / 3 : ℝ) = (X : ℝ) ^ (14 / 3 : ℝ) := by
    rw [← Real.rpow_natCast (X : ℝ) 4, ← Real.rpow_add hXR]
    norm_num
  calc
    ∑ m ∈ Icc 1 X, ((zeroChartFibers B m).card : ℝ) = (T.card : ℝ) := by
      simp only [T, card_sigma, Nat.cast_sum]
    _ ≤ 729 * q.totalDegree * (X : ℝ) ^ 4 *
        (3 * (X : ℝ) ^ (2 / 3 : ℝ)) := hsum.trans
      (mul_le_mul_of_nonneg_left hharm (by positivity))
    _ = _ := by rw [show 729 * (q.totalDegree : ℝ) * (X : ℝ) ^ 4 *
        (3 * (X : ℝ) ^ (2 / 3 : ℝ)) =
        2187 * q.totalDegree * ((X : ℝ) ^ 4 * (X : ℝ) ^ (2 / 3 : ℝ)) by ring, he]

end
end PierceLengthBound.FixedDividend
