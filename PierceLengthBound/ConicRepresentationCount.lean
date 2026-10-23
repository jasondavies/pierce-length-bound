/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicIntegerReduction
public import PierceLengthBound.ConicFactorHeight

/-! Lemma A.3 (`lem:jointconicdivisors`) for a rational function with a nonconstant reduced
denominator, represented by bounded integer polynomials that need not be coprime: common factors
are cancelled (the reduction step of Lemma A.2, `lem:jointconicproper`), and integrality is
read off any rational presentation whose denominator is nonzero at the counted parameters. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- Let `N / D = F / G` in `RatFunc ℚ`, with a nonconstant reduced denominator and `F, G`
integer polynomials of degree at most `d` and height at most `H` (not necessarily coprime).
The integers `t` with `D(t) ≠ 0` and `N(t)/D(t) ∈ ℤ` number at most
`2d · τmax((2d)! (2^d (d+1) H)^(2d))`. -/
theorem proper_integer_representation_card {F G : Polynomial ℤ} {N D : Polynomial ℚ}
    {d H : ℕ} (hD : D ≠ 0) (hH : 1 ≤ H)
    (hFd : F.natDegree ≤ d) (hGd : G.natDegree ≤ d)
    (hFH : ∀ n, |F.coeff n| ≤ H) (hGH : ∀ n, |G.coeff n| ≤ H)
    (hrep : algebraMap (Polynomial ℚ) (RatFunc ℚ) N / algebraMap (Polynomial ℚ) (RatFunc ℚ) D =
      algebraMap (Polynomial ℚ) (RatFunc ℚ) (F.map (Int.castRingHom ℚ)) /
        algebraMap (Polynomial ℚ) (RatFunc ℚ) (G.map (Int.castRingHom ℚ)))
    (hproper : 0 < (algebraMap (Polynomial ℚ) (RatFunc ℚ) N /
      algebraMap (Polynomial ℚ) (RatFunc ℚ) D).denom.natDegree)
    (S : Finset ℤ)
    (hvalue : ∀ t ∈ S, D.eval (t : ℚ) ≠ 0 ∧
      ∃ m : ℤ, N.eval (t : ℚ) = (m : ℚ) * D.eval (t : ℚ)) :
    S.card ≤ 2 * d * tauMax ((2 * d).factorial *
      (2 ^ d * (d + 1) * H) ^ (2 * d)) := by
  let φ := algebraMap (Polynomial ℚ) (RatFunc ℚ)
  have hφ := IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)
  have hmap := Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have hne : φ N / φ D ≠ 0 := by
    intro h
    change 0 < (φ N / φ D).denom.natDegree at hproper
    rw [h, RatFunc.denom_zero, natDegree_one] at hproper
    omega
  have hF : F ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero, map_zero, zero_div] at hrep
    exact hne hrep
  have hG : G ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero, map_zero, div_zero] at hrep
    exact hne hrep
  obtain ⟨F', G', hF'F, hG'G, hF'0, hG'0, hcop, hred⟩ := integer_rational_reduction F G hF hG
  have hrep' := hrep.trans hred
  have hGmap : G'.map (Int.castRingHom ℚ) ≠ 0 := by
    simpa only [Polynomial.map_zero] using hmap.ne hG'0
  have hDφ : φ D ≠ 0 := by simpa only [map_zero] using hφ.ne hD
  have hGφ : φ (G'.map (Int.castRingHom ℚ)) ≠ 0 := by
    simpa only [map_zero] using hφ.ne hGmap
  have hGpos : 0 < G'.natDegree := by
    have hdeg := natDegree_le_of_dvd
      (RatFunc.denom_div_dvd (F'.map (Int.castRingHom ℚ)) (G'.map (Int.castRingHom ℚ))) hGmap
    rw [natDegree_map_eq_of_injective Int.cast_injective] at hdeg
    rw [hrep'] at hproper
    omega
  apply reduced_integer_values_card hF hG hF'F hG'G hFd hGd hH hFH hGH hGpos hcop S
  intro t ht
  obtain ⟨htD, m, hm⟩ := hvalue t ht
  have hcross : N * G'.map (Int.castRingHom ℚ) = F'.map (Int.castRingHom ℚ) * D := by
    apply hφ
    simpa only [map_mul] using (div_eq_div_iff hDφ hGφ).mp hrep'
  have he := congrArg (Polynomial.eval (t : ℚ)) hcross
  simp only [eval_mul] at he
  have hv : (F'.map (Int.castRingHom ℚ)).eval (t : ℚ) =
      (m : ℚ) * (G'.map (Int.castRingHom ℚ)).eval (t : ℚ) := by
    apply mul_right_cancel₀ htD
    rw [← he, hm]
    ring
  have hFval := eval_map_apply (p := F') (Int.castRingHom ℚ) t
  have hGval := eval_map_apply (p := G') (Int.castRingHom ℚ) t
  change (F'.map (Int.castRingHom ℚ)).eval (t : ℚ) = ((F'.eval t : ℤ) : ℚ) at hFval
  change (G'.map (Int.castRingHom ℚ)).eval (t : ℚ) = ((G'.eval t : ℤ) : ℚ) at hGval
  rw [hFval, hGval] at hv
  have hvZ : F'.eval t = m * G'.eval t := by exact_mod_cast hv
  exact ⟨m, hvZ.trans (mul_comm _ _)⟩

end
end PierceLengthBound.FixedDividend
