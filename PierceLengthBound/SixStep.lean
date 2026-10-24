/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Window

/-!
# Six consecutive terms: a second positive integer

Let `x₀ > x₁ > ⋯ > x₅` be six consecutive terms of an orbit (`x₅` may be `0`) with quotients
`q, q+u, q+u+v, q+u+v+w, q+u+v+w+z`, and let `fₖ = xₖ - xₖ₊₁`. The curvatures of the three
overlapping blocks are `D = f₀v - f₁u`, `E = f₁w - f₂v`, `F = f₂z - f₃w`. Put
`S₀ = u²v + (u-1)v² + uw` and
`J = (u² + (u-1)v)z + w(u³ + uv(2u-1) + (u-1)v²) + w²((u-1)(u+v)+1)`.

The integer `L = (vw + w² + z)D - (u² + (u-1)v)E - w(wf₀ - uf₂)` satisfies
`q w L = J E + S₀ F` (`six_identity`), and `S(v,w,z) D - S₀ E = v L`. Since `E, F, J > 0`, we
get `L ≥ 1`, hence `q w ≤ J E + S₀ F` (`six_core`). This bounds `q ≍ a/A` by a polynomial in the
small parameters, with no divisor function, and gives `T⁶ A² ≤ 96·10⁶ a³`
(`six_step_bound`, Proposition 4.3). With the drop bound it gives the `3/10` window bound
`T¹⁰ ≤ 6144000000 a³ Δ²` (`window_bound`, Corollary 5.2), which proves Theorem 1.4.

Two consequences shared by the exponent arithmetic of the later window bounds close the file:
`window_facts` (the six-step and drop bounds force `A, Δ, a ≥ 1` and give `T² ≤ 8 A Δ`) and
`window_large_mean_gap` (`T⁴ ≤ 122449 a` when `A T > 28 a`).
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- `J(u, v, w, z)`. -/
def sixJ (u v w z : ℤ) : ℤ :=
  (u ^ 2 + (u - 1) * v) * z + w * (u ^ 3 + u * v * (2 * u - 1) + (u - 1) * v ^ 2) +
    w ^ 2 * ((u - 1) * (u + v) + 1)

/-- `S(u, v, w) = u²v + (u-1)v² + uw`. -/
def sixS (u v w : ℤ) : ℤ := u ^ 2 * v + (u - 1) * v ^ 2 + u * w

/-- The integer `L`, in terms of the drops `f₀ = x₀ - x₁`, `f₁`, `f₂`. -/
def sixL (u v w z f0 f1 f2 : ℤ) : ℤ :=
  (v * w + w ^ 2 + z) * (f0 * v - f1 * u) - (u ^ 2 + (u - 1) * v) * (f1 * w - f2 * v) -
    w * (w * f0 - u * f2)

/-- The six-step identity `q w L = J E + S₀ F`, from the division equations
(Lemma 4.1(2)). -/
theorem six_identity (a q u v w z x0 x1 x2 x3 x4 : ℤ)
    (h0 : x0 * q + x1 = a) (h1 : x1 * (q + u) + x2 = a) (h2 : x2 * (q + u + v) + x3 = a)
    (h3 : x3 * (q + u + v + w) + x4 = a) :
    q * w * sixL u v w z (x0 - x1) (x1 - x2) (x2 - x3) =
      sixJ u v w z * ((x1 - x2) * w - (x2 - x3) * v) +
        sixS u v w * ((x2 - x3) * z - (x3 - x4) * w) := by
  unfold sixL sixJ sixS
  linear_combination (-w * (u ^ 2 * v + u * v ^ 2 + u * w - v ^ 2)) * h3 +
    (w * (u ^ 2 * v + u ^ 2 * w + u * v ^ 2 + 2 * u * v * w + u * w ^ 2 + u * w + u * z - v ^ 2 -
      v * w)) * h2 +
    (-w * (u ^ 2 * w + 2 * u * v * w + u * w ^ 2 + u * z + v ^ 2 * w + v * w ^ 2 - v * w + v * z -
      w ^ 2)) * h1 +
    (w * (v ^ 2 * w + v * w ^ 2 + v * z - w ^ 2)) * h0

/-- `S(v,w,z) D - S(u,v,w) E = v L` (Lemma 4.1(1)). -/
theorem six_divisibility (u v w z f0 f1 f2 : ℤ) :
    sixS v w z * (f0 * v - f1 * u) - sixS u v w * (f1 * w - f2 * v) =
      v * sixL u v w z f0 f1 f2 := by
  unfold sixS sixL; ring

/-- `J > 0` for positive increments. -/
lemma sixJ_pos {u v w z : ℤ} (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hz : 1 ≤ z) :
    0 < sixJ u v w z := by
  unfold sixJ
  have hu0 : (0 : ℤ) ≤ u - 1 := by linarith
  have h1 : (0 : ℤ) < (u ^ 2 + (u - 1) * v) * z :=
    mul_pos (by nlinarith [mul_nonneg hu0 (by linarith : (0 : ℤ) ≤ v)]) (by linarith)
  have h2 : (0 : ℤ) ≤ w * (u ^ 3 + u * v * (2 * u - 1) + (u - 1) * v ^ 2) := by
    have : (0 : ℤ) ≤ u * v * (2 * u - 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have : (0 : ℤ) ≤ (u - 1) * v ^ 2 := mul_nonneg hu0 (sq_nonneg _)
    have : (0 : ℤ) ≤ u ^ 3 := by positivity
    exact mul_nonneg (by linarith) (by linarith)
  have h3 : (0 : ℤ) ≤ w ^ 2 * ((u - 1) * (u + v) + 1) := by
    have : (0 : ℤ) ≤ (u - 1) * (u + v) := mul_nonneg hu0 (by linarith)
    exact mul_nonneg (sq_nonneg _) (by linarith)
  linarith

/-- `S ≥ 0` for positive increments. -/
lemma sixS_nonneg {u v w : ℤ} (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) : 0 ≤ sixS u v w := by
  unfold sixS
  have : (0 : ℤ) ≤ (u - 1) * v ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have : (0 : ℤ) ≤ u ^ 2 * v := mul_nonneg (sq_nonneg _) (by linarith)
  have : (0 : ℤ) ≤ u * w := mul_nonneg (by linarith) (by linarith)
  linarith

/-- `J ≤ 9 m³ w` when `1 ≤ u, v, w, z ≤ m`. -/
lemma sixJ_le {u v w z m : ℤ} (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hz : 1 ≤ z)
    (hum : u ≤ m) (hvm : v ≤ m) (hwm : w ≤ m) (hzm : z ≤ m) : sixJ u v w z ≤ 9 * m ^ 3 * w := by
  have hm1 : 1 ≤ m := hu.trans hum
  have hu0 : (0 : ℤ) ≤ u - 1 := by linarith
  have hm3 : (0 : ℤ) ≤ m ^ 3 := by positivity
  have b1 : m ^ 3 ≤ m ^ 3 * w := le_mul_of_one_le_right hm3 hw
  have a1 : u ^ 2 * z ≤ m ^ 3 := by
    calc u ^ 2 * z ≤ m ^ 2 * m := by gcongr
      _ = m ^ 3 := by ring
  have a2 : (u - 1) * v * z ≤ m ^ 3 := by
    calc (u - 1) * v * z ≤ m * m * m := by gcongr; linarith
      _ = m ^ 3 := by ring
  have a3 : u ^ 3 + u * v * (2 * u - 1) + (u - 1) * v ^ 2 ≤ 4 * m ^ 3 := by
    have c1 : u ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ (by linarith) hum 3
    have c2 : u * v * (2 * u - 1) ≤ m * m * (2 * m) := by gcongr <;> linarith
    have c3 : (u - 1) * v ^ 2 ≤ m * m ^ 2 := by gcongr; linarith
    linarith
  have a4 : w * ((u - 1) * (u + v) + 1) ≤ 2 * m ^ 3 := by
    have c1 : (u - 1) * (u + v) ≤ (m - 1) * (2 * m) := by gcongr; linarith
    have c0 : (0 : ℤ) ≤ (u - 1) * (u + v) := mul_nonneg hu0 (by linarith)
    have c2 : w * ((u - 1) * (u + v) + 1) ≤ m * ((m - 1) * (2 * m) + 1) := by
      gcongr
    nlinarith
  calc sixJ u v w z = u ^ 2 * z + (u - 1) * v * z +
        w * (u ^ 3 + u * v * (2 * u - 1) + (u - 1) * v ^ 2) +
        w * (w * ((u - 1) * (u + v) + 1)) := by unfold sixJ; ring
    _ ≤ m ^ 3 * w + m ^ 3 * w + w * (4 * m ^ 3) + w * (2 * m ^ 3) := by
        have := a1.trans b1
        have := a2.trans b1
        have := mul_le_mul_of_nonneg_left a3 (by linarith : (0 : ℤ) ≤ w)
        have := mul_le_mul_of_nonneg_left a4 (by linarith : (0 : ℤ) ≤ w)
        linarith
    _ = 9 * m ^ 3 * w - m ^ 3 * w := by ring
    _ ≤ 9 * m ^ 3 * w := by nlinarith

/-- `S ≤ 3 m³ w` when `1 ≤ u, v, w ≤ m`. -/
lemma sixS_le {u v w m : ℤ} (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hum : u ≤ m) (hvm : v ≤ m) (hwm : w ≤ m) : sixS u v w ≤ 3 * m ^ 3 * w := by
  have hm1 : 1 ≤ m := hu.trans hum
  have hm3 : (0 : ℤ) ≤ m ^ 3 := by positivity
  have b1 : m ^ 3 ≤ m ^ 3 * w := le_mul_of_one_le_right hm3 hw
  have c1 : u ^ 2 * v ≤ m ^ 3 := by
    calc u ^ 2 * v ≤ m ^ 2 * m := by gcongr
      _ = m ^ 3 := by ring
  have c2 : (u - 1) * v ^ 2 ≤ m ^ 3 := by
    calc (u - 1) * v ^ 2 ≤ m * m ^ 2 := by gcongr; linarith
      _ = m ^ 3 := by ring
  have c3 : u * w ≤ m ^ 3 := by
    calc u * w ≤ m * m := by gcongr
      _ ≤ m * m * m := le_mul_of_one_le_right (by positivity) hm1
      _ = m ^ 3 := by ring
  unfold sixS
  linarith

/-- **The six-step inequality** (Corollary 4.2). For six consecutive terms with `q ≥ 1` and
quotient increments `1 ≤ u, v, w, z ≤ m`, the curvatures `E, F` of the blocks starting at `x₁`
and `x₂` (natural-number differences, which are positive) satisfy `E x₃ ≤ (v+1)(x₁-x₄)²`,
`F x₄ ≤ (w+1)(x₂-x₅)²` and `q ≤ 9 m³ E + 3 m³ F`. -/
theorem six_core (a q u v w z x0 x1 x2 x3 x4 x5 m : ℕ)
    (h0 : x0 * q + x1 = a) (h1 : x1 * (q + u) + x2 = a) (h2 : x2 * (q + u + v) + x3 = a)
    (h3 : x3 * (q + u + v + w) + x4 = a) (h4 : x4 * (q + u + v + w + z) + x5 = a)
    (_h01 : x1 < x0) (h12 : x2 < x1) (h23 : x3 < x2) (h34 : x4 < x3) (h45 : x5 < x4)
    (hq : 1 ≤ q) (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hz : 1 ≤ z)
    (hum : u ≤ m) (hvm : v ≤ m) (hwm : w ≤ m) (hzm : z ≤ m) :
    ((x1 - x2) * w - (x2 - x3) * v) * x3 ≤ (v + 1) * (x1 - x4) ^ 2 ∧
    ((x2 - x3) * z - (x3 - x4) * w) * x4 ≤ (w + 1) * (x2 - x5) ^ 2 ∧
    q ≤ 9 * m ^ 3 * ((x1 - x2) * w - (x2 - x3) * v) +
      3 * m ^ 3 * ((x2 - x3) * z - (x3 - x4) * w) := by
  -- the blocks starting at `x₁` and `x₂`
  have bE := block_core a x4 (x3 - x4) (x2 - x3) (x1 - x2) (q + u) v w (by omega) (by omega) hv
    (by rw [show x4 + (x3 - x4) + (x2 - x3) + (x1 - x2) = x1 by omega,
      show x4 + (x3 - x4) + (x2 - x3) = x2 by omega]; exact h1)
    (by rw [show x4 + (x3 - x4) + (x2 - x3) = x2 by omega, show x4 + (x3 - x4) = x3 by omega]
        exact h2)
    (by rw [show x4 + (x3 - x4) = x3 by omega]; exact h3)
  have bF := block_core a x5 (x4 - x5) (x3 - x4) (x2 - x3) (q + u + v) w z (by omega) (by omega)
    hw
    (by rw [show x5 + (x4 - x5) + (x3 - x4) + (x2 - x3) = x2 by omega,
      show x5 + (x4 - x5) + (x3 - x4) = x3 by omega]; exact h2)
    (by rw [show x5 + (x4 - x5) + (x3 - x4) = x3 by omega, show x5 + (x4 - x5) = x4 by omega]
        exact h3)
    (by rw [show x5 + (x4 - x5) = x4 by omega]; exact h4)
  obtain ⟨hEpos, hEle⟩ := bE
  obtain ⟨hFpos, hFle⟩ := bF
  rw [show x4 + (x3 - x4) = x3 by omega,
    show x1 - x2 + (x2 - x3) + (x3 - x4) = x1 - x4 by omega] at hEle
  rw [show x5 + (x4 - x5) = x4 by omega,
    show x2 - x3 + (x3 - x4) + (x4 - x5) = x2 - x5 by omega] at hFle
  refine ⟨hEle, hFle, ?_⟩
  -- pass to `ℤ`
  set E := (x1 - x2) * w - (x2 - x3) * v with hE
  set F := (x2 - x3) * z - (x3 - x4) * w with hF
  have cE : (E : ℤ) = ((x1 : ℤ) - x2) * w - ((x2 : ℤ) - x3) * v := by
    rw [hE, Nat.cast_sub hEpos.le]; push_cast [h12.le, h23.le]; ring
  have cF : (F : ℤ) = ((x2 : ℤ) - x3) * z - ((x3 : ℤ) - x4) * w := by
    rw [hF, Nat.cast_sub hFpos.le]; push_cast [h23.le, h34.le]; ring
  have hE1 : (1 : ℤ) ≤ E := by exact_mod_cast (show 1 ≤ E by omega)
  have hF1 : (1 : ℤ) ≤ F := by exact_mod_cast (show 1 ≤ F by omega)
  have z0 : (x0 : ℤ) * q + x1 = a := by exact_mod_cast h0
  have z1 : (x1 : ℤ) * ((q : ℤ) + u) + x2 = a := by exact_mod_cast h1
  have z2 : (x2 : ℤ) * ((q : ℤ) + u + v) + x3 = a := by exact_mod_cast h2
  have z3 : (x3 : ℤ) * ((q : ℤ) + u + v + w) + x4 = a := by exact_mod_cast h3
  have hid := six_identity a q u v w z x0 x1 x2 x3 x4 z0 z1 z2 z3
  rw [← cE, ← cF] at hid
  generalize sixL u v w z (x0 - x1) (x1 - x2) (x2 - x3) = L at hid
  generalize hJz : sixJ u v w z = Jz at hid
  generalize hS : sixS u v w = S0 at hid
  generalize hEz : (E : ℤ) = Ez at hid hE1
  generalize hFz : (F : ℤ) = Fz at hid hF1
  have hu' : (1 : ℤ) ≤ u := by exact_mod_cast hu
  have hv' : (1 : ℤ) ≤ v := by exact_mod_cast hv
  have hw' : (1 : ℤ) ≤ w := by exact_mod_cast hw
  have hz' : (1 : ℤ) ≤ z := by exact_mod_cast hz
  have hum' : (u : ℤ) ≤ m := by exact_mod_cast hum
  have hvm' : (v : ℤ) ≤ m := by exact_mod_cast hvm
  have hwm' : (w : ℤ) ≤ m := by exact_mod_cast hwm
  have hzm' : (z : ℤ) ≤ m := by exact_mod_cast hzm
  have hJpos : 0 < Jz := hJz ▸ sixJ_pos hu' hv' hw' hz'
  have hS0pos : 0 ≤ S0 := hS ▸ sixS_nonneg hu' hv' hw'
  have hJle : Jz ≤ 9 * m ^ 3 * w := hJz ▸ sixJ_le hu' hv' hw' hz' hum' hvm' hwm' hzm'
  have hS0le : S0 ≤ 3 * m ^ 3 * w := hS ▸ sixS_le hu' hv' hw' hum' hvm' hwm'
  -- `L ≥ 1`
  have hL1 : 1 ≤ L := by
    have hpos : 0 < (q : ℤ) * w * L := by
      rw [hid]
      have := mul_pos hJpos (by linarith : (0 : ℤ) < Ez)
      have := mul_nonneg hS0pos (by linarith : (0 : ℤ) ≤ Fz)
      linarith
    have hqw : (0 : ℤ) < q * w := by
      have : (1 : ℤ) ≤ q := by exact_mod_cast hq
      positivity
    have : 0 < L := pos_of_mul_pos_right hpos hqw.le
    omega
  -- conclude `q w ≤ J E + S₀ F ≤ (9 m³ E + 3 m³ F) w`, and cancel `w`
  have key : (q : ℤ) * w ≤ (9 * m ^ 3 * Ez + 3 * m ^ 3 * Fz) * w := by
    have hE0 : (0 : ℤ) ≤ Ez := by linarith
    have hF0 : (0 : ℤ) ≤ Fz := by linarith
    calc (q : ℤ) * w = q * w * 1 := by ring
      _ ≤ q * w * L := by gcongr
      _ = Jz * Ez + S0 * Fz := hid
      _ ≤ (9 * m ^ 3 * w) * Ez + (3 * m ^ 3 * w) * Fz := by gcongr
      _ = (9 * m ^ 3 * Ez + 3 * m ^ 3 * Fz) * w := by ring
  have : (q : ℤ) ≤ 9 * m ^ 3 * Ez + 3 * m ^ 3 * Fz := le_of_mul_le_mul_right key (by linarith)
  rw [← hEz, ← hFz] at this
  exact_mod_cast this

/-- **The six-step window bound.** `T⁶ A² ≤ 96·10⁶ a³` for `T ≥ 10`, with no divisor loss. -/
theorem six_step_bound {a A T : ℕ} {g : ℕ → ℕ} (W : Window a A T g) (hT : 10 ≤ T) :
    T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3 := by
  classical
  have hA := W.one_le
  have ha := W.one_le_a (by omega)
  -- a run of six terms with total drop `s` satisfying `s T ≤ 10 A`
  obtain ⟨j, hjJ, hjs⟩ : ∃ j ∈ range (T - 5), (g j - g (j + 5)) * (T - 5) ≤ 5 * A - 5 := by
    apply exists_le_of_sum_le (nonempty_range_iff.mpr (by omega))
    rw [← sum_mul, sum_const, card_range, smul_eq_mul]
    have := W.sum_five_drops (T - 5) (by omega)
    have := W.mem 0 (by omega); have := W.mem 1 (by omega); have := W.mem 2 (by omega)
    have := W.mem 3 (by omega); have := W.mem 4 (by omega)
    have := W.mem (T - 5) (by omega); have := W.mem (T - 5 + 1) (by omega)
    have := W.mem (T - 5 + 2) (by omega); have := W.mem (T - 5 + 3) (by omega)
    have := W.mem (T - 5 + 4) (by omega)
    have hs : ∑ i ∈ range (T - 5), (g i - g (i + 5)) ≤ 5 * A - 5 := by omega
    calc (∑ i ∈ range (T - 5), (g i - g (i + 5))) * (T - 5) ≤ (5 * A - 5) * (T - 5) :=
          Nat.mul_le_mul_right _ hs
      _ = (T - 5) * (5 * A - 5) := by ring
  have hjT := mem_range.mp hjJ
  set s := g j - g (j + 5) with hs
  have hsT : s * T ≤ 10 * A := by
    have : s * T ≤ 2 * (s * (T - 5)) := by
      have : T ≤ 2 * (T - 5) := by omega
      calc s * T ≤ s * (2 * (T - 5)) := Nat.mul_le_mul_left _ this
        _ = 2 * (s * (T - 5)) := by ring
    omega
  -- the terms, quotients and increments
  have m0 := W.mem j (by omega)
  have m1 := W.mem (j + 1) (by omega)
  have m2 := W.mem (j + 2) (by omega)
  have m3 := W.mem (j + 3) (by omega)
  have m4 := W.mem (j + 4) (by omega)
  have m5 := W.mem (j + 5) (by omega)
  have l01 := W.succ_lt (j := j) (by omega)
  have l12 : g (j + 2) < g (j + 1) := W.succ_lt (j := j + 1) (by omega)
  have l23 : g (j + 3) < g (j + 2) := W.succ_lt (j := j + 2) (by omega)
  have l34 : g (j + 4) < g (j + 3) := W.succ_lt (j := j + 3) (by omega)
  have l45 : g (j + 5) < g (j + 4) := W.succ_lt (j := j + 4) (by omega)
  have q01 : a / g j < a / g (j + 1) := W.quot_lt (by omega)
  have q12 : a / g (j + 1) < a / g (j + 2) := W.quot_lt (j := j + 1) (by omega)
  have q23 : a / g (j + 2) < a / g (j + 3) := W.quot_lt (j := j + 2) (by omega)
  have q34 : a / g (j + 3) < a / g (j + 4) := W.quot_lt (j := j + 3) (by omega)
  have q45 : a / g (j + 4) < a / g (j + 5) := W.quot_lt (j := j + 4) (by omega)
  have hu : (a / g (j + 1) - a / g j) * (g (j + 1) * g j) ≤ a * (g j - g (j + 2)) :=
    W.incr_mul_le (by omega)
  have hv : (a / g (j + 2) - a / g (j + 1)) * (g (j + 2) * g (j + 1)) ≤
      a * (g (j + 1) - g (j + 3)) := W.incr_mul_le (j := j + 1) (by omega)
  have hw : (a / g (j + 3) - a / g (j + 2)) * (g (j + 3) * g (j + 2)) ≤
      a * (g (j + 2) - g (j + 4)) := W.incr_mul_le (j := j + 2) (by omega)
  have hz : (a / g (j + 4) - a / g (j + 3)) * (g (j + 4) * g (j + 3)) ≤
      a * (g (j + 3) - g (j + 5)) := W.incr_mul_le (j := j + 3) (by omega)
  have hdiv : ∀ k, k ≤ 4 → g (j + k) * (a / g (j + k)) + g (j + k + 1) = a := by
    intro k hk
    rw [W.step (j + k) (by omega)]
    exact Nat.div_add_mod a _
  set q := a / g j with hqd
  set u := a / g (j + 1) - a / g j with hud
  set v := a / g (j + 2) - a / g (j + 1) with hvd
  set w := a / g (j + 3) - a / g (j + 2) with hwd
  set z := a / g (j + 4) - a / g (j + 3) with hzd
  set m := max (max u v) (max w z)
  have hq1 : 1 ≤ q := (Nat.le_div_iff_mul_le (W.pos (by omega))).mpr (by
    simpa using W.le_a j (by omega))
  have h0 := hdiv 0 (by norm_num)
  have h1 : g (j + 1) * (q + u) + g (j + 2) = a := by
    rw [show q + u = a / g (j + 1) by omega]; exact hdiv 1 (by norm_num)
  have h2 : g (j + 2) * (q + u + v) + g (j + 3) = a := by
    rw [show q + u + v = a / g (j + 2) by omega]; exact hdiv 2 (by norm_num)
  have h3 : g (j + 3) * (q + u + v + w) + g (j + 4) = a := by
    rw [show q + u + v + w = a / g (j + 3) by omega]; exact hdiv 3 (by norm_num)
  have h4 : g (j + 4) * (q + u + v + w + z) + g (j + 5) = a := by
    rw [show q + u + v + w + z = a / g (j + 4) by omega]; exact hdiv 4 (by norm_num)
  simp only [add_zero] at h0
  obtain ⟨hE, hF, hqEF⟩ := six_core a q u v w z (g j) (g (j + 1)) (g (j + 2)) (g (j + 3))
    (g (j + 4)) (g (j + 5)) m h0 h1 h2 h3 h4 l01 l12 l23 l34 l45 hq1 (by omega) (by omega)
    (by omega) (by omega) (by simp [m]) (by simp [m]) (by simp [m]) (by simp [m])
  set E := (g (j + 1) - g (j + 2)) * w - (g (j + 2) - g (j + 3)) * v
  set F := (g (j + 2) - g (j + 3)) * z - (g (j + 3) - g (j + 4)) * w
  -- size of the increments: `(each) · A T ≤ 10 a`
  have cancel : ∀ y : ℕ, y * (A * A) ≤ a * s → y * (A * T) ≤ 10 * a := by
    intro y hy
    have : y * (A * T) * A ≤ 10 * a * A := by
      calc y * (A * T) * A = y * (A * A) * T := by ring
        _ ≤ a * s * T := Nat.mul_le_mul_right _ hy
        _ = a * (s * T) := by ring
        _ ≤ a * (10 * A) := Nat.mul_le_mul_left _ hsT
        _ = 10 * a * A := by ring
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have inc : ∀ (y k : ℕ), k ≤ 3 → y * (g (j + k + 1) * g (j + k)) ≤ a
      * (g (j + k) - g (j + k + 2)) →
      y * (A * T) ≤ 10 * a := by
    intro y k hk hy
    apply cancel
    have hk0 := W.mem (j + k) (by omega)
    have hk1 := W.mem (j + k + 1) (by omega)
    have hd : g (j + k) - g (j + k + 2) ≤ s := by
      have := W.le_of_le (i := j) (j := j + k) (by omega) (by omega)
      have := W.le_of_le (i := j + k + 2) (j := j + 5) (by omega) (by omega)
      omega
    calc y * (A * A) ≤ y * (g (j + k + 1) * g (j + k)) := Nat.mul_le_mul_left _
           (Nat.mul_le_mul hk1.1 hk0.1)
      _ ≤ a * (g (j + k) - g (j + k + 2)) := hy
      _ ≤ a * s := Nat.mul_le_mul_left _ hd
  have iu := inc u 0 (by norm_num) (by simpa using hu)
  have iv := inc v 1 (by norm_num) hv
  have iw := inc w 2 (by norm_num) hw
  have iz := inc z 3 (by norm_num) hz
  have hmAT : m * (A * T) ≤ 10 * a := by
    simp only [m]
    rcases le_total u v with h | h <;> rcases le_total w z with h' | h' <;>
      simp only [max_eq_left, max_eq_right, h, h'] <;>
      first
      | (rcases le_total v z with h'' | h'' <;> simp only [h'', sup_of_le_left, sup_of_le_right] <;>
          assumption)
      | (rcases le_total v w with h'' | h'' <;> simp only [h'', sup_of_le_left, sup_of_le_right] <;>
          assumption)
      | (rcases le_total u z with h'' | h'' <;> simp only [h'', sup_of_le_left, sup_of_le_right] <;>
          assumption)
      | (rcases le_total u w with h'' | h'' <;> simp only [h'', sup_of_le_left, sup_of_le_right] <;>
          assumption)
  -- `E A ≤ 2 m s²`, `F A ≤ 2 m s²`
  have hvm : v ≤ m := by simp [m]
  have hwm : w ≤ m := by simp [m]
  have hEA : E * A ≤ 2 * m * s ^ 2 := by
    have hd : g (j + 1) - g (j + 4) ≤ s := by omega
    calc E * A ≤ E * g (j + 3) := Nat.mul_le_mul_left _ m3.1
      _ ≤ (v + 1) * (g (j + 1) - g (j + 4)) ^ 2 := hE
      _ ≤ (2 * m) * s ^ 2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hd 2)
  have hFA : F * A ≤ 2 * m * s ^ 2 := by
    have hd : g (j + 2) - g (j + 5) ≤ s := by omega
    calc F * A ≤ F * g (j + 4) := Nat.mul_le_mul_left _ m4.1
      _ ≤ (w + 1) * (g (j + 2) - g (j + 5)) ^ 2 := hF
      _ ≤ (2 * m) * s ^ 2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hd 2)
  have hqA : q * A ≤ 24 * m ^ 4 * s ^ 2 := by
    calc q * A ≤ (9 * m ^ 3 * E + 3 * m ^ 3 * F) * A := Nat.mul_le_mul_right _ hqEF
      _ = 9 * m ^ 3 * (E * A) + 3 * m ^ 3 * (F * A) := by ring
      _ ≤ 9 * m ^ 3 * (2 * m * s ^ 2) + 3 * m ^ 3 * (2 * m * s ^ 2) := by gcongr
      _ = 24 * m ^ 4 * s ^ 2 := by ring
  -- `a ≤ 4 A q`
  have haq : a ≤ 4 * A * q := le_four_mul h0 l01 m0.2 hq1
  -- assemble
  have k1 : q * A * (A ^ 4 * T ^ 6) ≤ 24000000 * a ^ 4 * A ^ 2 := by
    calc q * A * (A ^ 4 * T ^ 6) ≤ 24 * m ^ 4 * s ^ 2 * (A ^ 4 * T ^ 6) :=
          Nat.mul_le_mul_right _ hqA
      _ = 24 * (m * (A * T)) ^ 4 * (s * T) ^ 2 := by ring
      _ ≤ 24 * (10 * a) ^ 4 * (10 * A) ^ 2 := by gcongr
      _ = 24000000 * a ^ 4 * A ^ 2 := by ring
  have k2 : q * A ^ 3 * T ^ 6 ≤ 24000000 * a ^ 4 := by
    have : q * A ^ 3 * T ^ 6 * A ^ 2 ≤ 24000000 * a ^ 4 * A ^ 2 := by
      calc q * A ^ 3 * T ^ 6 * A ^ 2 = q * A * (A ^ 4 * T ^ 6) := by ring
        _ ≤ _ := k1
    exact Nat.le_of_mul_le_mul_right this (by positivity)
  have k3 : T ^ 6 * A ^ 2 * a ≤ 96000000 * a ^ 3 * a := by
    calc T ^ 6 * A ^ 2 * a ≤ T ^ 6 * A ^ 2 * (4 * A * q) := Nat.mul_le_mul_left _ haq
      _ = 4 * (q * A ^ 3 * T ^ 6) := by ring
      _ ≤ 4 * (24000000 * a ^ 4) := Nat.mul_le_mul_left _ k2
      _ = 96000000 * a ^ 3 * a := by ring
  exact Nat.le_of_mul_le_mul_right k3 (by omega)

/-- **The window bound.** `T¹⁰ ≤ 6144000000 a³ Δ²` for `T ≥ 10` (Corollary 5.2): the six-step
bound times the square of the drop bound eliminates `A`. -/
theorem window_bound {a A T Δ : ℕ} {g : ℕ → ℕ} (W : Window a A T g) (hΔ : DivBound a Δ)
    (hT : 10 ≤ T) : T ^ 10 ≤ 6144000000 * a ^ 3 * Δ ^ 2 := by
  have h1 := drop_bound W hΔ (by omega)
  have h2 := six_step_bound W hT
  have hA := W.one_le
  have h3 : T ≤ 2 * (T - 1) := by omega
  have key : T ^ 10 * A ^ 2 ≤ 6144000000 * a ^ 3 * Δ ^ 2 * A ^ 2 := by
    calc T ^ 10 * A ^ 2 = T ^ 6 * A ^ 2 * T ^ 2 * T ^ 2 := by ring
      _ ≤ T ^ 6 * A ^ 2 * T ^ 2 * (2 * (T - 1)) ^ 2 := by gcongr
      _ = 4 * (T ^ 6 * A ^ 2) * (T * (T - 1)) ^ 2 := by ring
      _ ≤ 4 * (96000000 * a ^ 3) * (4 * A * Δ) ^ 2 := by gcongr
      _ = 6144000000 * a ^ 3 * Δ ^ 2 * A ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- The size facts shared by the exponent arithmetic of the window bounds: the six-step and drop
bounds force `A, Δ, a ≥ 1`, and give `T² ≤ 8 A Δ`. -/
lemma window_facts {a A T Δ : ℕ} (hT : 2 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3)
    (hdrop : T * (T - 1) ≤ 4 * A * Δ) : 1 ≤ A ∧ 1 ≤ Δ ∧ 1 ≤ a ∧ T ^ 2 ≤ 8 * A * Δ := by
  obtain ⟨hA, hΔ, hT2⟩ := drop_bound_sq hT hdrop
  exact ⟨hA, hΔ, Nat.pos_of_ne_zero fun h => by simp [h] at hsix; omega, hT2⟩

/-- **A large mean gap.** If `A T > 28 a`, the six-step bound gives `T⁴ ≤ 122449 a`. -/
lemma window_large_mean_gap {a A T : ℕ} (ha : 1 ≤ a)
    (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hbig : 28 * a < A * T) :
    T ^ 4 ≤ 122449 * a := by
  have h1 : (784 * T ^ 4) * a ^ 2 ≤ (784 * (122449 * a)) * a ^ 2 := by
    calc (784 * T ^ 4) * a ^ 2 = (28 * a) ^ 2 * T ^ 4 := by ring
      _ ≤ (A * T) ^ 2 * T ^ 4 := by gcongr
      _ = T ^ 6 * A ^ 2 := by ring
      _ ≤ 96000000 * a ^ 3 := hsix
      _ ≤ (784 * (122449 * a)) * a ^ 2 := by ring_nf; omega
  have := Nat.le_of_mul_le_mul_right h1 (by positivity)
  omega

end PierceLengthBound
