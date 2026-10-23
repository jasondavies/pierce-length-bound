/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftConicSlack
public import PierceLengthBound.OrbitGapCoordinates

/-! The conic divisor estimate (`orbit_conic_points_slow`) as a count of distinct complete gap
vectors: one start is chosen for each gap vector (`gap_image_representatives`), and the node
points of these starts are distinct. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- Uniform subpolynomial counting for the gap vectors on a fixed nonexceptional conic
(affine Hilbert degree `2`). Repeated starts with the same gaps are counted once. -/
theorem orbit_conic_gap_count_slow :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ {a b i : ℕ}, b < a → i + 7 < P a b →
      ∀ {X : ℕ}, 1 ≤ X → (∀ j, |theta a b i j| ≤ X) → X ≤ 10 ^ 16 * a ^ 7 →
      NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i) →
      ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
        orbitCurveQuadraticQ a b i ∈ I → orbitCurveEquationQ a b i ∈ I →
        (∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = 2 * m + c) →
        orbitFreeNodesQ a b i ∈ coordinateZeroLocus I →
        ∀ G : Finset ℕ, (∀ l ∈ G, l + 7 < P a b) →
          (∀ l ∈ G, theta a b i = theta a b l) →
          (∀ l ∈ G, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
          (G.image (kap a b)).card ≤ R a := by
  obtain ⟨R, hR, hcount⟩ := orbit_conic_points_slow
  refine ⟨R, hR, ?_⟩
  intro a b i hba hi X hX ht hXb hne I hI hf hg hd hzi G hmargin hθ hz
  let : I.IsPrime := hI
  obtain ⟨N, c, hdegree⟩ := hd
  obtain ⟨l, hl, _hk, hinj⟩ := gap_image_representatives hba G
    (fun l hl => by have := hmargin l hl; omega) hθ
  have hc := hcount hba hi hX ht hXb hne I hf hg hdegree hzi l
    (fun j => hmargin _ (hl j)) (fun j => hθ _ (hl j)) (fun j => hz _ (hl j)) hinj
  simpa only [Fintype.card_coe] using hc

end
end PierceLengthBound.FixedDividend
