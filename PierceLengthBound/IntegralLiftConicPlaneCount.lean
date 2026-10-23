/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftConicCount

/-! The conic count of `IntegralLiftConicCount` with the containing plane constructed from
three of the orbit points (Lemma A.1, `lem:jointconicparameter`): free nodes are bounded by `a`,
so the plane has height at most `24a³`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- The integer free nodes of an orbit state are bounded by `a`. -/
lemma orbitFreeNodesZ_bound (a b i : ℕ) (j : Fin 3) : |orbitFreeNodesZ a b i j| ≤ a := by
  have h1 : qq a b (i + (j.val + 1)) ≤ a := Nat.div_le_self ..
  have h0 : qq a b i ≤ a := Nat.div_le_self ..
  unfold orbitFreeNodesZ
  rw [abs_le]
  constructor <;> omega

/-- The conic count without a plane: three of the orbit points span an integer plane of
height at most `24a³` containing the component, so the states number at most
`492 + integerValueSlack D C e (conicInputHeight a X (24a³))`. -/
theorem orbit_conic_points_bound :
    ∃ D C e : ℕ, 1 ≤ C ∧ ∀  {a b i : ℕ} (_hba : b < a)
    (_hi : i + 7 < P a b) {X : ℕ} (_hX : 1 ≤ X)
    (_ht : ∀ j, |theta a b i j| ≤ X)
    (_hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (_hf : orbitCurveQuadraticQ a b i ∈ I) (_hg : orbitCurveEquationQ a b i ∈ I)
    {N : ℕ} {c : ℤ}
    (_hdegree : ∀ m ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = 2 * m + c)
    (_hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    {ι : Type*} [Fintype ι] (l : ι → ℕ)
    (_hl : ∀ j, l j + 7 < P a b) (_hθ : ∀ j, theta a b i = theta a b (l j))
    (_hpoints : ∀ j, orbitFreeNodesQ a b (l j) ∈ coordinateZeroLocus I)
    (_hinj : Function.Injective (fun j => orbitFreeNodesQ a b (l j))) ,
      Fintype.card ι ≤ 492 + integerValueSlack D C e (conicInputHeight a X (24 * a ^ 3)) := by
  obtain ⟨D, C, e, hC, hbound⟩ := orbit_conic_integer_points_bound
  refine ⟨D, C, e, hC, ?_⟩
  intro a b i hba hi X hX ht hne I hprime hf hg N c hdegree hx ι hι l hl hθ hpoints hinj
  classical
  by_cases hcard : Fintype.card ι ≤ 492
  · omega
  obtain ⟨f⟩ : Nonempty (Fin 3 ↪ ι) := Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_fin]; omega)
  have hZinj : Function.Injective (fun j : ι => orbitFreeNodesZ a b (l j)) := by
    intro j k hjk
    dsimp only at hjk
    apply hinj
    change orbitFreeNodesQ a b (l j) = orbitFreeNodesQ a b (l k)
    rw [← orbitFreeNodesZ_cast a b (l j), ← orbitFreeNodesZ_cast a b (l k), hjk]
  have hZ : ∀ j, (fun k => (orbitFreeNodesZ a b (l j) k : ℚ)) ∈ coordinateZeroLocus I := by
    intro j
    rw [orbitFreeNodesZ_cast]
    exact hpoints j
  obtain ⟨n, eplane, hn, hnb, heb, hplane⟩ := degree_two_integer_plane_height I
    ⟨N, c, hdegree⟩ (by omega : 1 ≤ a) (hZinj.comp f.injective)
    (fun j k => orbitFreeNodesZ_bound a b (l (f j)) k) (fun j => hZ (f j))
  apply hbound hba hi hX (by have : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ (by omega); omega)
    ht hne I hf hg n eplane hn _ _ hplane hdegree hx l hl hθ hpoints hinj
  · intro j
    have hpow : (a : ℤ) ^ 2 ≤ a ^ 3 := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ a by omega))
      (by decide : 2 ≤ 3)
    push_cast
    nlinarith [hnb j, sq_nonneg (a : ℤ)]
  · simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using heb

end
end PierceLengthBound.FixedDividend
