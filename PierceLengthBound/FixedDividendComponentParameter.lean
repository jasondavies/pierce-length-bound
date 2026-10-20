/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendOrbitConicModel

/-! Bounded quadratic integer parametrizations of actual component point sets. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
set_option maxHeartbeats 1000000

/-- A certified integral plane-conic model gives bounded quadratic numerators
for every integral component point, and an injective integer parameter. -/
theorem component_integer_parameter
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) (n : Fin 3 → ℤ) (e : ℤ)
    (hplane : integerPlanePolynomial n e ∈ I)
    (σ : Fin 3 ≃ Fin 3) (v : Fin 6 → ℤ) {K L : ℕ}
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hn : n (σ 2) ≠ 0)
    (hnb : ∀ j, |n j| ≤ L) (heb : |e| ≤ L) (hvb : ∀ j, |v j| ≤ K)
    (hα : v 0 ≠ 0) (hΔ : (v 1) ^ 2 - 4 * v 0 * v 2 = 0)
    (hJ : 2 * v 1 * v 3 - 4 * v 0 * v 4 ≠ 0)
    (hconic : ∀ z : Fin 3 → ℤ, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I →
      conicValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (z (σ 0)) (z (σ 1)) = 0) :
    ∃ (E : ℤ) (N : Fin 3 → Polynomial ℤ), E ≠ 0 ∧ |E| ≤ 12 * (L : ℤ) * K ^ 3 ∧
      (∀ j, (N j).natDegree ≤ 2) ∧
      (∀ j k, |(N j).coeff k| ≤ 33 * (L : ℤ) * K ^ 3) ∧ (N 1).coeff 2 ≠ 0 ∧
      (∀ z : Fin 3 → ℤ, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I →
        ∀ j, E * z (σ j) = (N j).eval (2 * v 0 * z (σ 0) + v 1 * z (σ 1) + v 3)) ∧
      Set.InjOn (fun z : Fin 3 → ℤ => 2 * v 0 * z (σ 0) + v 1 * z (σ 1) + v 3)
        {z | (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I} := by
  have hp (z : Fin 3 → ℤ) (hz : (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I) :
      n (σ 2) * z (σ 2) + n (σ 0) * z (σ 0) + n (σ 1) * z (σ 1) + e = 0 := by
    have hh := hz _ hplane
    rw [integerPlanePolynomial_eval] at hh
    have hdot : dot3 n z + e = 0 := by exact_mod_cast hh
    have hsum := σ.sum_comp (fun j => n j * z j)
    simp only [Fin.sum_univ_succ,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hsum
    dsimp [dot3] at hdot
    linear_combination hdot + hsum
  obtain ⟨E, N, hE, hEb, hNd, hNb, hN2, hrepr, hinj⟩ :=
    parabola_integer_parameter_height hK hL hα hn hJ hΔ
      (hvb 0) (hvb 1) (hvb 3) (hvb 4) (hvb 5)
      (hnb (σ 2)) (hnb (σ 0)) (hnb (σ 1)) heb
  refine ⟨E, N, hE, hEb, hNd, hNb, hN2, ?_, ?_⟩
  · intro z hz
    exact hrepr (z ∘ σ) (hconic z hz) (hp z hz)
  · intro z hz t ht heq
    have hzt : z ∘ σ = t ∘ σ :=
      hinj ⟨hconic z hz, hp z hz⟩ ⟨hconic t ht, hp t ht⟩ heq
    funext j
    obtain ⟨k, rfl⟩ := σ.surjective j
    exact congrFun hzt k

end
end PierceLengthBound.FixedDividend
