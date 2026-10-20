module

public import AffineCurveCounting.PlaneStepanovDimension

/-! The explicit real-valued error term for the integer Stepanov parameters. -/

@[expose] public section
namespace AffineCurveCounting

lemma stepanov_real_bound (d p A D N t : ℕ) (hd : 0 < d)
    (hp : 27 * d ^ 4 < p) (hD : d * D < p)
    (hN : N + 4 * d ^ 2 = d * A) (hNpos : 0 < N)
    (hpx : p < (d * A + d) ^ 2)
    (hcount : t * N ≤ d * (D + p * A) + d * (d - 1) * N) :
    (t : ℝ) ≤ p + 161 * (d : ℝ) ^ 2 * Real.sqrt p := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hdR]
  have hdle : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hdR]
  have hpR : 27 * (d : ℝ) ^ 4 < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by nlinarith only [hpR, pow_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) 4]
  let s := Real.sqrt (p : ℝ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = p := Real.sq_sqrt (le_of_lt hp0)
  have hs1 : 1 ≤ s := by nlinarith only [hs0, hs2, hpR, hd2]
  have hNR : (N : ℝ) + 4 * (d : ℝ) ^ 2 = (d : ℝ) * A := by exact_mod_cast hN
  have hpxR : (p : ℝ) < ((d : ℝ) * A + d) ^ 2 := by exact_mod_cast hpx
  have hxp0 : (0 : ℝ) ≤ (d : ℝ) * A + d := by positivity
  have hsnear : s < (N : ℝ) + 5 * (d : ℝ) ^ 2 := by
    have hh : s < (d : ℝ) * A + d := by nlinarith only [hpxR, hs2, hs0, hxp0]
    nlinarith only [hh, hNR, hdle]
  have hsN : s < 32 * (N : ℝ) := by
    by_contra! hn
    have hh : 31 * s < 160 * (d : ℝ) ^ 2 := by linarith only [hn, hsnear]
    have hsq := mul_self_lt_mul_self (by positivity : 0 ≤ 31 * s) hh
    nlinarith only [hsq, hpR, hs2]
  have hsp : (p : ℝ) ≤ 32 * N * s := by
    have hh := mul_le_mul_of_nonneg_right (le_of_lt hsN) hs0
    nlinarith only [hh, hs2]
  have hcoef : 4 * (d : ℝ) ^ 2 + 1 ≤ 5 * (d : ℝ) ^ 2 := by linarith only [hd2]
  have hprod1 := mul_le_mul_of_nonneg_right hcoef (le_of_lt hp0)
  have hprod2 := mul_le_mul_of_nonneg_left hsp (by positivity : 0 ≤ 5 * (d : ℝ) ^ 2)
  have hsmall := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ (d : ℝ) ^ 2 * N)
  have hsub : d * (d - 1) ≤ d ^ 2 := by nlinarith only [Nat.sub_le d 1]
  have hc : t * N ≤ d * D + p * (d * A) + d ^ 2 * N := by
    have hh := Nat.mul_le_mul_right N hsub
    nlinarith only [hcount, hh]
  have hcR : (t : ℝ) * N ≤ (d : ℝ) * D + p * ((d : ℝ) * A) + (d : ℝ) ^ 2 * N := by
    exact_mod_cast hc
  have hDR : (d : ℝ) * D ≤ p := by exact_mod_cast hD.le
  rw [← hNR] at hcR
  have hfin : (t : ℝ) * N ≤ (p + 161 * (d : ℝ) ^ 2 * s) * N := by
    nlinarith only [hcR, hDR, hprod1, hprod2, hsmall]
  exact (mul_le_mul_iff_left₀ (by exact_mod_cast hNpos : (0 : ℝ) < N)).mp hfin

end AffineCurveCounting
