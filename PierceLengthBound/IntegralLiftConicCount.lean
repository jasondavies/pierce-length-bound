/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftCoefficientHeight
public import PierceLengthBound.ConicRepresentationCount

/-! Uniform divisor bounds for actual orbit points on nonexceptional conics. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial
set_option maxHeartbeats 1000000

lemma orbitLift_polynomials_congr {a b i l : ℕ} (h : theta a b i = theta a b l) :
    orbitLiftNumeratorQ a b i = orbitLiftNumeratorQ a b l ∧
    orbitLiftDenominatorQ a b i = orbitLiftDenominatorQ a b l := by
  obtain ⟨_, hρ, hu, hv, hρ', hu', hv'⟩ := orbit_pattern_eq_of_theta h
  simp only [orbitLiftNumeratorQ, orbitLiftDenominatorQ, orbitCurveCofactorsQ,
    hρ, hu, hv, hρ', hu', hv', and_self]

lemma orbitLift_parameter_integer_value {a b i l : ℕ} (hba : b < a)
    (hl : l + 7 < P a b) (hθ : theta a b i = theta a b l)
    (z : Fin 3 → Polynomial ℚ) (t : ℤ)
    (hz : ∀ j, (z j).eval (t : ℚ) = orbitFreeNodesQ a b l j) :
    (MvPolynomial.aeval z (orbitLiftDenominatorQ a b i)).eval (t : ℚ) ≠ 0 ∧
      ∃ m : ℤ, (MvPolynomial.aeval z (orbitLiftNumeratorQ a b i)).eval (t : ℚ) =
        (m : ℚ) * (MvPolynomial.aeval z (orbitLiftDenominatorQ a b i)).eval (t : ℚ) := by
  obtain ⟨hn, hd⟩ := orbitLift_polynomials_congr hθ
  simp only [polynomial_substitution_eval, hn, hd,
    show (fun j => (z j).eval (t : ℚ)) = orbitFreeNodesQ a b l from funext hz]
  obtain ⟨hD, he⟩ := orbitLift_evaluation hba hl
  exact ⟨hD, integralLiftCoordinate a b l, ((eq_div_iff hD).mp he).symm⟩

/-- The constants are uniform in the dividend, component, and bounded plane.
The finite exceptional alternative is included explicitly in the bound. -/
theorem orbit_conic_integer_points_bound :
    ∃ D C e : ℕ, 1 ≤ C ∧ ∀  {a b i : ℕ} (_hba : b < a)
    (_hi : i + 7 < P a b) {X L : ℕ} (_hX : 1 ≤ X) (_hL : 1 ≤ L)
    (_ht : ∀ j, |theta a b i j| ≤ X)
    (_hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (_hf : orbitCurveQuadraticQ a b i ∈ I) (_hg : orbitCurveEquationQ a b i ∈ I)
    (n : Fin 3 → ℤ) (eplane : ℤ) (_hn : n ≠ 0) (_hnb : ∀ j, |n j| ≤ L) (_heb : |eplane| ≤ L)
    (_hplane : integerPlanePolynomial n eplane ∈ I)
    {N : ℕ} {c : ℤ}
    (_hdegree : ∀ m ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = 2 * m + c)
    (_hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    {ι : Type*} [Fintype ι] (l : ι → ℕ)
    (_hl : ∀ j, l j + 7 < P a b) (_hθ : ∀ j, theta a b i = theta a b (l j))
    (_hpoints : ∀ j, orbitFreeNodesQ a b (l j) ∈ coordinateZeroLocus I)
    (_hinj : Function.Injective (fun j => orbitFreeNodesQ a b (l j))) ,
      Fintype.card ι ≤ 492 + integerValueSlack D C e (conicInputHeight a X L) := by
  obtain ⟨D, C, e, hC, hheight⟩ := orbitLift_bounded_parameter_height
  refine ⟨D, 2 ^ D * (D + 1) * C, e, by
    have hp : 1 ≤ 2 ^ D := Nat.one_le_pow _ _ (by decide)
    exact Nat.mul_le_mul (Nat.mul_le_mul hp (show 1 ≤ D + 1 by omega)) hC, ?_⟩
  intro a b i hba hi X L hX hL ht hne I hprime hf hg n eplane hn hnb heb hplane N c hdegree hx
    ι hι l hl hθ hpoints hinj
  classical
  by_cases hcard : Fintype.card ι ≤ 492
  · omega
  obtain ⟨σ, v, E, F, hσ, hE, hvb, hEb, hFd, hFb, hrepr, hp_inj, hgap, hproper, hden⟩ :=
    orbit_bounded_integer_parameter_proper hba hi hX hL ht hne I hf hg n eplane hn hnb heb
      hplane hdegree hx l hl hθ hpoints hinj (by omega)
  obtain ⟨A, B, hAd, hBd, hAc, hBc, hrep⟩ := hheight hba hi ht σ E F hE hEb hFd hFb
  let p : (Fin 3 → ℤ) → ℤ := fun w => 2 * v 0 * w (σ 0) + v 1 * w (σ 1) + v 3
  let z := normalizedParameter σ E F
  have hZ : ∀ j, (fun k => (orbitFreeNodesZ a b (l j) k : ℚ)) ∈ coordinateZeroLocus I := by
    intro j
    rw [orbitFreeNodesZ_cast]
    exact hpoints j
  let t : ι → ℤ := fun j => p (orbitFreeNodesZ a b (l j))
  have ht_inj : Function.Injective t := by
    intro j k hjk
    have hw := hp_inj (hZ j) (hZ k) hjk
    apply hinj
    change orbitFreeNodesQ a b (l j) = orbitFreeNodesQ a b (l k)
    rw [← orbitFreeNodesZ_cast a b (l j), ← orbitFreeNodesZ_cast a b (l k), hw]
  have hzeval (j : ι) : ∀ k, (z k).eval (t j : ℚ) = orbitFreeNodesQ a b (l j) k := by
    intro k
    exact (normalizedParameter_eval σ hE F _ (t j) (hrepr _ (hZ j)) k).trans
      (congrFun (orbitFreeNodesZ_cast a b (l j)) k)
  let S : Finset ℤ := Finset.univ.image t
  have hScard : S.card = Fintype.card ι := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ ht_inj, Finset.card_univ]
  have hvalue : ∀ s ∈ S,
      (MvPolynomial.aeval z (orbitLiftDenominatorQ a b i)).eval (s : ℚ) ≠ 0 ∧
      ∃ m : ℤ, (MvPolynomial.aeval z (orbitLiftNumeratorQ a b i)).eval (s : ℚ) =
        (m : ℚ) * (MvPolynomial.aeval z (orbitLiftDenominatorQ a b i)).eval (s : ℚ) := by
    intro s hs
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
    exact orbitLift_parameter_integer_value hba (hl j) (hθ j) z (t j) (hzeval j)
  have hD : MvPolynomial.aeval z (orbitLiftDenominatorQ a b i) ≠ 0 := by
    have hpos : 0 < S.card := by omega
    obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
    intro h
    exact (hvalue s hs).1 (by simp only [h, eval_zero])
  have hM : 1 ≤ conicInputHeight a X L := by unfold conicInputHeight; omega
  have hcount := proper_integer_representation_card hD
    (by have hp := Nat.one_le_pow e _ hM; nlinarith : 1 ≤ C * conicInputHeight a X L ^ e)
    hAd hBd hAc hBc hrep hproper S hvalue
  have hcount' : S.card ≤ integerValueSlack D (2 ^ D * (D + 1) * C) e
      (conicInputHeight a X L) := by
    simpa only [integerValueSlack, mul_pow, ← pow_mul, mul_assoc] using hcount
  omega

end
end PierceLengthBound.FixedDividend
