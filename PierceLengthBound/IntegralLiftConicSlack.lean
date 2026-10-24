/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftConicPlaneCount

/-! The per-conic bound of Proposition 8.10 (`prop:jointconic`): when the pattern height is at
most `10¹⁶ a⁷`, a nonexceptional conic carries the free nodes of at most `R(a)` orbit states of
the same pattern, with `R` of slow growth. The conic count of `IntegralLiftConicPlaneCount` is
bounded by an explicit `conicPointSlack` in `a` alone. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial

/-- `integerValueSlack d C e` is monotone. -/
lemma integerValueSlack_mono (d C e : ℕ) {a b : ℕ} (h : a ≤ b) :
    integerValueSlack d C e a ≤ integerValueSlack d C e b := by
  apply Nat.mul_le_mul_left
  apply Finset.sup_le
  intro n hn
  apply tau_le_tauMax
  have hn' : n ≤ (2 * d).factorial * C ^ (2 * d) * a ^ (e * (2 * d)) := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  exact hn'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _))

/-- For `X ≤ c a^k`, the conic input height with plane height `24a³` is at most a fixed
multiple of `a^(24k + 22)`. -/
lemma conicInputHeight_polynomial_bound {a X c k : ℕ} (ha : 1 ≤ a) (hX : X ≤ c * a ^ k) :
    conicInputHeight a X (24 * a ^ 3) ≤
      (2 + c + 33 * 10 ^ 3 * 12 ^ 6 * 24 ^ 7 * c ^ 24) * a ^ (24 * k + 22) := by
  let K := 33 * 10 ^ 3 * 12 ^ 6 * 24 ^ 7
  have hexpand : conicInputHeight a X (24 * a ^ 3) = 1 + a + X + K * X ^ 24 * a ^ 21 := by
    dsimp [conicInputHeight, K]
    ring
  have h1 : 1 ≤ a ^ (24 * k + 22) := Nat.one_le_pow _ _ ha
  have ha' : a ≤ a ^ (24 * k + 22) := by
    simpa only [pow_one] using Nat.pow_le_pow_right ha (show 1 ≤ 24 * k + 22 by omega)
  have hX' : X ≤ c * a ^ (24 * k + 22) := hX.trans
    (Nat.mul_le_mul_left c (Nat.pow_le_pow_right ha (by omega)))
  have hlarge : K * X ^ 24 * a ^ 21 ≤ K * c ^ 24 * a ^ (24 * k + 22) := by
    calc K * X ^ 24 * a ^ 21 ≤ K * (c * a ^ k) ^ 24 * a ^ 21 := by gcongr
      _ = K * c ^ 24 * a ^ (24 * k + 21) := by
        rw [mul_pow, ← pow_mul, ← mul_assoc, mul_assoc (K * c ^ 24), ← pow_add]
        congr 2
        omega
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right ha (by omega))
  rw [hexpand]
  dsimp only [K] at hlarge ⊢
  nlinarith

lemma integerValueSlack_polynomial (d C e c k a : ℕ) :
    integerValueSlack d C e (c * a ^ k) = integerValueSlack d (C * c ^ e) (k * e) a := by
  simp only [integerValueSlack, mul_pow, ← pow_mul, mul_assoc]

/-- The conic count bound as a function of `a`, for pattern height `X ≤ c a^k`. -/
def conicPointSlack (d C e c k a : ℕ) : ℕ :=
  492 + integerValueSlack d (C * (2 + c + 33 * 10 ^ 3 * 12 ^ 6 * 24 ^ 7 * c ^ 24) ^ e)
    ((24 * k + 22) * e) a

/-- `conicPointSlack d C e c k` grows slowly in `a`. -/
theorem conicPointSlack_slow (d C e c k : ℕ) : SlowGrowth (conicPointSlack d C e c k) := by
  intro η hη
  obtain ⟨B, hB, hb⟩ := integerValueSlack_slow d
    (C * (2 + c + 33 * 10 ^ 3 * 12 ^ 6 * 24 ^ 7 * c ^ 24) ^ e) ((24 * k + 22) * e) η hη
  refine ⟨492 + B, by positivity, fun a ha => ?_⟩
  have hp := Real.one_le_rpow (by exact_mod_cast ha : (1 : ℝ) ≤ a) hη.le
  have hb' := hb a ha
  unfold conicPointSlack
  simp only [Nat.cast_add, Nat.cast_ofNat]
  nlinarith

/-- For `X ≤ c a^k`, the conic count bound of `orbit_conic_points_bound` is at most
`conicPointSlack d C e c k a`. -/
theorem conic_count_le_slack {a X c k : ℕ} (ha : 1 ≤ a) (hX : X ≤ c * a ^ k)
    (d C e : ℕ) :
    492 + integerValueSlack d C e (conicInputHeight a X (24 * a ^ 3)) ≤
      conicPointSlack d C e c k a := by
  have h := integerValueSlack_mono d C e (conicInputHeight_polynomial_bound ha hX)
  rw [integerValueSlack_polynomial] at h
  exact Nat.add_le_add_left h 492

/-- There is a slowly growing `R` such that, for every nonexceptional pattern at `i` of height
`X ≤ 10¹⁶ a⁷` and every degree-two prime component `I` of the pattern curve through the free
nodes at `i`, the states with the same `θ` whose free nodes are distinct points of `I` number at
most `R a`. -/
theorem orbit_conic_points_slow :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀  {a b i : ℕ} (_hba : b < a)
    (_hi : i + 7 < P a b) {X : ℕ} (_hX : 1 ≤ X)
    (_ht : ∀ j, |theta a b i j| ≤ X) (_hXb : X ≤ 10 ^ 16 * a ^ 7)
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
      Fintype.card ι ≤ R a := by
  obtain ⟨D, C, e, hC, hcount⟩ := orbit_conic_points_bound
  refine ⟨conicPointSlack D C e (10 ^ 16) 7, conicPointSlack_slow D C e (10 ^ 16) 7, ?_⟩
  intro a b i hba hi X hX ht hXb hne I hprime hf hg N c hdegree hx ι hι l hl hθ hpoints hinj
  exact (hcount hba hi hX ht hne I hf hg hdegree hx l hl hθ hpoints hinj).trans
    (conic_count_le_slack (by omega : 1 ≤ a) hXb D C e)

end PierceLengthBound.FixedDividend
