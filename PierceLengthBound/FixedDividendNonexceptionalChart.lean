/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendEventualGeneration
public import PierceLengthBound.FixedDividendComponents

/-!
# The first-node chart coordinate is nonzero

Positive Hilbert slope and eventual generation by the first node force the
chart coordinate to be nonzero in the affine coordinate ring.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Positive Hilbert slope and eventual generation force the chart coordinate
itself to be nonzero in the affine coordinate ring. -/
theorem first_node_ne_zero_of_generation {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin 3) K)) {d N M : ℕ} {b : ℤ}
    (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (hspan : ∀ n ≥ M, filteredCoordinateSpace I (n + 1) ⊔
        (filteredCoordinateSpace I (n + 1)).map
          (LinearMap.mulLeft K (Ideal.Quotient.mk I (X 0))) =
      filteredCoordinateSpace I (n + 2)) :
    Ideal.Quotient.mk I (X 0) ≠ 0 := by
  intro hz
  let n := max N M
  have hnN : N ≤ n := le_max_left _ _
  have hnM : M ≤ n := le_max_right _ _
  have hs := hspan n hnM
  rw [hz] at hs
  have hzL : LinearMap.mulLeft K (0 : MvPolynomial (Fin 3) K ⧸ I) = 0 := by
    ext x
    simp
  rw [hzL, Submodule.map_zero, sup_bot_eq] at hs
  have he := congrArg
    (fun V : Submodule K (MvPolynomial (Fin 3) K ⧸ I) => (Module.finrank K V : ℤ)) hs
  have h1 := hdegree (n + 1) (by omega)
  have h2 := hdegree (n + 2) (by omega)
  rw [h1, h2] at he
  push_cast at he
  have : (0 : ℤ) < d := by exact_mod_cast hd
  nlinarith

end
end PierceLengthBound.FixedDividend
