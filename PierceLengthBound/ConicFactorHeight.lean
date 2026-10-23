/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicResultantHeight
public import PierceLengthBound.BranchSieveFactorHeight

/-! The integer-value count of Lemma A.3 (`lem:jointconicdivisors`) for a coprime pair
`F' ∣ F`, `G' ∣ G` obtained by cancelling common factors (the cancellation step of Lemma A.2,
`lem:jointconicproper`). The heights of `F'` and `G'` are controlled through the Mahler-measure
factor estimate `branch_integer_factor_coeff_height`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

/-- If `F' ∣ F` and `G' ∣ G` with `F, G` nonzero of degree at most `d` and height at most `H`,
and `F', G'` are coprime over `ℚ` with `G'` nonconstant, then the integers `t` with
`G'(t) ∣ F'(t)` number at most `2d · τmax((2d)! (2^d (d+1) H)^(2d))`. -/
theorem reduced_integer_values_card {F G F' G' : ℤ[X]} {d H : ℕ}
    (hF : F ≠ 0) (hG : G ≠ 0) (hF' : F' ∣ F) (hG' : G' ∣ G)
    (hFd : F.natDegree ≤ d) (hGd : G.natDegree ≤ d) (hH : 1 ≤ H)
    (hFH : ∀ n, |F.coeff n| ≤ H) (hGH : ∀ n, |G.coeff n| ≤ H)
    (hGpos : 0 < G'.natDegree)
    (hcop : IsCoprime (F'.map (Int.castRingHom ℚ)) (G'.map (Int.castRingHom ℚ)))
    (S : Finset ℤ) (hdiv : ∀ t ∈ S, G'.eval t ∣ F'.eval t) :
    S.card ≤ 2 * d * tauMax ((2 * d).factorial *
      (2 ^ d * (d + 1) * H) ^ (2 * d)) := by
  have hheight : 1 ≤ 2 ^ d * (d + 1) * H := by
    have : 0 < H := by omega
    exact Nat.succ_le_of_lt (by positivity)
  apply integer_values_card_of_height hheight
    ((natDegree_le_of_dvd hF' hF).trans hFd) ((natDegree_le_of_dvd hG' hG).trans hGd)
    hGpos (branch_integer_factor_coeff_height F hF hFd hFH F' hF')
    (branch_integer_factor_coeff_height G hG hGd hGH G' hG') hcop S hdiv

end
end PierceLengthBound.FixedDividend
