/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendComponentParameter

/-! Complete bounded integer parametrization of actual nonexceptional conic points. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial
set_option maxHeartbeats 1000000

/-- Every integral point of the actual degree-two component has a bounded
quadratic representation in an injective integer parameter. -/
theorem orbit_bounded_integer_parameter {a b i : ℕ} (hba : b < a)
    (hi : i + 7 < P a b) {X L : ℕ} (hX : 1 ≤ X) (hL : 1 ≤ L)
    (ht : ∀ j, |theta a b i j| ≤ X)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (n : Fin 3 → ℤ) (e : ℤ) (hn : n ≠ 0) (hnb : ∀ j, |n j| ≤ L) (heb : |e| ≤ L)
    (hplane : integerPlanePolynomial n e ∈ I)
    {N : ℕ} {c : ℤ}
    (hdegree : ∀ m ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = 2 * m + c)
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I) :
    ∃ (σ : Fin 3 ≃ Fin 3) (v : Fin 6 → ℤ) (E : ℤ) (F : Fin 3 → Polynomial ℤ),
      σ 1 = 0 ∧ E ≠ 0 ∧
      (∀ j, |v j| ≤ 10 * (12 * (X : ℤ) ^ 4) ^ 2 * L ^ 2) ∧
      |E| ≤ 12 * (L : ℤ) * (10 * (12 * X ^ 4) ^ 2 * L ^ 2) ^ 3 ∧
      (∀ j, (F j).natDegree ≤ 2) ∧
      (∀ j k, |(F j).coeff k| ≤ 33 * (L : ℤ) * (10 * (12 * X ^ 4) ^ 2 * L ^ 2) ^ 3) ∧
      (F 1).coeff 2 ≠ 0 ∧
      (∀ z : Fin 3 → ℤ, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I →
        ∀ j, E * z (σ j) = (F j).eval (2 * v 0 * z (σ 0) + v 1 * z (σ 1) + v 3)) ∧
      Set.InjOn (fun z : Fin 3 → ℤ => 2 * v 0 * z (σ 0) + v 1 * z (σ 1) + v 3)
        {z | (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I} := by
  obtain ⟨j, k, v, hbij, hnk, hvb, hα, hΔ, hJ, hconic⟩ :=
    orbit_bounded_integer_conic_model hba hi (by exact_mod_cast hX)
      (by positivity : (0 : ℤ) ≤ L) ht hne I hf hg n e hn hnb heb hplane hdegree hx
  let σ : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![j, 0, k] hbij
  have hσ0 : σ 0 = j := rfl
  have hσ1 : σ 1 = 0 := rfl
  have hσ2 : σ 2 = k := rfl
  let K : ℕ := 10 * (12 * X ^ 4) ^ 2 * L ^ 2
  have hK : 1 ≤ K := by
    have hX0 : 0 < X := by omega
    have hL0 : 0 < L := by omega
    have hK0 : 0 < K := by dsimp [K]; positivity
    omega
  have hvK : ∀ j, |v j| ≤ (K : ℤ) := by
    simpa only [K, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hvb
  obtain ⟨E, F, hE, hEb, hFd, hFb, hF2, hrepr, hinj⟩ :=
    component_integer_parameter I n e hplane σ v hK hL (by simpa only [hσ2] using hnk)
      hnb heb hvK hα hΔ hJ (by simpa only [hσ0, hσ1] using hconic)
  refine ⟨σ, v, E, F, hσ1, hE, hvb, ?_, hFd, ?_, hF2, hrepr, hinj⟩
  · simpa only [K, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hEb
  · simpa only [K, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hFb

end
end PierceLengthBound.FixedDividend
