/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendConicIntegralCoefficients

/-! Polynomial height bounds for the explicitly cleared conic coefficients. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- A single polynomial bound for all six cleared binary coefficients. -/
theorem integralPlaneConicCoefficients_height
    {a b c l0 l1 l2 D n0 n1 n2 e B L : ℤ}
    (hB : 1 ≤ B) (hL : 0 ≤ L)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B) (hD : |D| ≤ B)
    (hl0 : |l0| ≤ B) (hl1 : |l1| ≤ B) (hl2 : |l2| ≤ B)
    (hn0 : |n0| ≤ L) (hn1 : |n1| ≤ L) (hn2 : |n2| ≤ L) (he : |e| ≤ L) :
    ∀ j, |integralPlaneConicCoefficients a b c l0 l1 l2 D n0 n1 n2 e j| ≤
      10 * B ^ 2 * L ^ 2 := by
  let P := B ^ 2 * L ^ 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hfour {x y z w : ℤ} (hx : |x| ≤ B) (hy : |y| ≤ B)
      (hz : |z| ≤ L) (hw : |w| ≤ L) : |x * y * z * w| ≤ P := by
    calc |x * y * z * w| = |x| * |y| * |z| * |w| := by simp only [abs_mul]
      _ ≤ B * B * L * L := by gcongr
      _ = P := by dsimp [P]; ring
  have hthree {x z w : ℤ} (hx : |x| ≤ B) (hz : |z| ≤ L) (hw : |w| ≤ L) :
      |x * z * w| ≤ P := by
    simpa using hfour hx (show |(1 : ℤ)| ≤ B by simpa using hB) hz hw
  have hdiff {x y z w : ℤ} (hx : |x| ≤ B) (hy : |y| ≤ B)
      (hz : |z| ≤ L) (hw : |w| ≤ L) : |x * z - y * w| ≤ 2 * B * L := by
    calc |x * z - y * w| ≤ |x * z| + |y * w| := by
          simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (x * z) 0 (y * w)
      _ = |x| * |z| + |y| * |w| := by simp only [abs_mul]
      _ ≤ B * L + B * L := by gcongr
      _ = _ := by ring
  have hpair {x y : ℤ} (hx : |x| ≤ 2 * B * L) (hy : |y| ≤ 2 * B * L) :
      |x * y| ≤ 4 * P := by
    calc |x * y| = |x| * |y| := abs_mul ..
      _ ≤ (2 * B * L) * (2 * B * L) := by gcongr
      _ = _ := by dsimp [P]; ring
  have hmixed {x y z : ℤ} (hx : |x| ≤ B) (hy : |y| ≤ L)
      (hz : |z| ≤ 2 * B * L) : |x * y * z| ≤ 2 * P := by
    calc |x * y * z| = |x| * |y| * |z| := by simp only [abs_mul]
      _ ≤ B * L * (2 * B * L) := by gcongr
      _ = _ := by dsimp [P]; ring
  have hsum3 {x y z : ℤ} : |x + y + z| ≤ |x| + |y| + |z| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hlin {x y z w : ℤ} : |x - y + z - w| ≤ |x| + |y| + |z| + |w| := by
    calc |x - y + z - w| ≤ |x - y + z| + |w| := by
          simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (x - y + z) 0 w
      _ ≤ |x - y| + |z| + |w| := by gcongr; exact abs_add_le _ _
      _ ≤ |x| + |y| + |z| + |w| := by
        gcongr
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le x 0 y
  have hM0 := hdiff ha hc hn2 hn0
  have hM1 := hdiff hb hc hn2 hn1
  have hquad {x n : ℤ} (hx : |x| ≤ B) (hn : |n| ≤ L) :
      |x * D * n2 ^ 2 + c * D * n ^ 2 + (x * n2 - c * n) ^ 2| ≤ 6 * P := by
    have h1 := hfour hx hD hn2 hn2
    have h2 := hfour hc hD hn hn
    have h3 := hpair (hdiff hx hc hn2 hn) (hdiff hx hc hn2 hn)
    have h4 := hsum3 (x := x * D * n2 ^ 2) (y := c * D * n ^ 2)
      (z := (x * n2 - c * n) ^ 2)
    rw [show x * D * n2 * n2 = x * D * n2 ^ 2 by ring] at h1
    rw [show c * D * n * n = c * D * n ^ 2 by ring] at h2
    rw [← pow_two] at h3
    linarith
  have hlinear {x l n : ℤ} (hx : |x| ≤ B) (hl : |l| ≤ B) (hn : |n| ≤ L) :
      |2 * c * D * n * e - 2 * c * e * (x * n2 - c * n) +
        l * n2 ^ 2 - l2 * n * n2| ≤ 8 * P := by
    have h1 := hfour hc hD hn he
    have h2 := hmixed hc he (hdiff hx hc hn2 hn)
    have h3 := hthree hl hn2 hn2
    have h4 := hthree hl2 hn hn2
    have h5 := hlin (x := 2 * c * D * n * e)
      (y := 2 * c * e * (x * n2 - c * n)) (z := l * n2 ^ 2) (w := l2 * n * n2)
    norm_num only [abs_mul, abs_pow, Int.reduceAbs] at h1 h2 h3 h4 h5
    nlinarith only [h1, h2, h3, h4, h5]
  intro j
  fin_cases j
  · change |b * D * n2 ^ 2 + c * D * n1 ^ 2 + (b * n2 - c * n1) ^ 2| ≤ 10 * B ^ 2 * L ^ 2
    have hh := hquad hb hn1
    dsimp [P] at hh hP
    nlinarith only [hh, hP]
  · change |2 * c * D * n0 * n1 + 2 * (a * n2 - c * n0) * (b * n2 - c * n1)| ≤ 10 * B ^ 2 * L ^ 2
    have h1 := hfour hc hD hn0 hn1
    have h2 := hpair hM0 hM1
    have h3 := abs_add_le (2 * c * D * n0 * n1)
      (2 * (a * n2 - c * n0) * (b * n2 - c * n1))
    norm_num only [abs_mul, Int.reduceAbs] at h1 h2 h3
    dsimp [P] at h1 h2
    nlinarith only [h1, h2, h3]
  · change |a * D * n2 ^ 2 + c * D * n0 ^ 2 + (a * n2 - c * n0) ^ 2| ≤ 10 * B ^ 2 * L ^ 2
    have hh := hquad ha hn0
    dsimp [P] at hh hP
    nlinarith only [hh, hP]
  · change |2 * c * D * n1 * e - 2 * c * e * (b * n2 - c * n1) +
      l1 * n2 ^ 2 - l2 * n1 * n2| ≤ 10 * B ^ 2 * L ^ 2
    have hh := hlinear hb hl1 hn1
    dsimp [P] at hh hP
    nlinarith only [hh, hP]
  · change |2 * c * D * n0 * e - 2 * c * e * (a * n2 - c * n0) +
      l0 * n2 ^ 2 - l2 * n0 * n2| ≤ 10 * B ^ 2 * L ^ 2
    have hh := hlinear ha hl0 hn0
    dsimp [P] at hh hP
    nlinarith only [hh, hP]
  · change |c * D * e ^ 2 + (c * e) ^ 2 - l2 * e * n2| ≤ 10 * B ^ 2 * L ^ 2
    have h1 := hfour hc hD he he
    have h2 := hfour hc hc he he
    have h3 := hthree hl2 he hn2
    have h4 := abs_sub_le (c * D * e ^ 2 + (c * e) ^ 2) 0 (l2 * e * n2)
    have h5 := abs_add_le (c * D * e ^ 2) ((c * e) ^ 2)
    simp only [sub_zero, zero_sub, abs_neg] at h4
    rw [show c * D * e * e = c * D * e ^ 2 by ring] at h1
    rw [show c * c * e * e = (c * e) ^ 2 by ring] at h2
    dsimp [P] at h1 h2 h3 hP
    nlinarith only [h1, h2, h3, h4, h5, hP]

end
end PierceLengthBound.FixedDividend
