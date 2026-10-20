/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendTranscendentalCoordinate

/-!
# Bounding the number of prime curve components

Separators and a transcendental coordinate on each component give independent
families of arbitrary length. The filtered coordinate-space slope consequently
bounds the number of components, without assuming existence of Hilbert polynomials.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Separating polynomials times powers of transcendental coordinates are jointly
independent in the original quotient coordinate ring. -/
theorem separated_component_powers_independent {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (S : Finset (Ideal (MvPolynomial σ K)))
    (hS : ∀ p : S, p.val.IsPrime ∧ I ≤ p.val)
    (r : S → MvPolynomial σ K) (hr : ∀ p, r p ∉ p.val)
    (hoff : ∀ p q : S, p ≠ q → r q ∈ p.val)
    (j : S → σ) (hj : ∀ p, Transcendental K ((Ideal.Quotient.mk p.val) (X (j p)))) (m : ℕ) :
    LinearIndependent K (fun t : S × Fin (m + 1) =>
      (Ideal.Quotient.mk I) (r t.1 * X (j t.1) ^ t.2.val)) := by
  classical
  let inst (p : S) : p.val.IsPrime := (hS p).1
  apply linearIndependent_of_separating_maps (K := K) (V := MvPolynomial σ K ⧸ I)
    (ι := S) (κ := Fin (m + 1))
    (fun p : S => MvPolynomial σ K ⧸ p.val)
    (fun p => (Ideal.Quotient.factorₐ K (hS p).2).toLinearMap)
    (fun p k => (Ideal.Quotient.mk I) (r p * X (j p) ^ k.val))
  · intro p q hpq k
    change (Ideal.Quotient.mk p.val) (r q * X (j q) ^ k.val) = 0
    rw [map_mul, (Ideal.Quotient.eq_zero_iff_mem.mpr (hoff p q hpq)), zero_mul]
  · intro p
    change LinearIndependent K (fun k : Fin (m + 1) =>
      (Ideal.Quotient.mk p.val) (r p * X (j p) ^ k.val))
    simp only [map_mul, map_pow]
    have hp0 : (Ideal.Quotient.mk p.val) (r p) ≠ 0 := by
      exact fun h => hr p (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hpow := (transcendental_powers_independent (hj p)).comp
      (fun k : Fin (m + 1) => k.val) Fin.val_injective
    have h := hpow.map' (LinearMap.mulLeft K ((Ideal.Quotient.mk p.val) (r p)))
      (LinearMap.ker_eq_bot.mpr (fun x y h => mul_left_cancel₀ hp0 h))
    simpa [Function.comp_def, LinearMap.mulLeft_apply] using h

/-- A linear filtered-space bound controls minimal primes with a transcendental coordinate. -/
theorem minimalPrime_card_le_of_transcendental_coordinates {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin 3) K)) (S : Finset (Ideal (MvPolynomial (Fin 3) K)))
    (hS : ∀ p ∈ S, p ∈ I.minimalPrimes ∧ p.height = 2)
    (htrans : ∀ p ∈ S, ∃ j : Fin 3, Transcendental K ((Ideal.Quotient.mk p) (X j)))
    (C : ℕ) (hbound : ∀ N, 14 ≤ N → Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 2)) :
    S.card ≤ C := by
  classical
  have hsep (p : S) : ∃ r : MvPolynomial (Fin 3) K,
      r ∉ p.val ∧ ∀ q ∈ S, q ≠ p.val → r ∈ q :=
    exists_component_separator I S (fun q hq => (hS q hq).1) p.property
  choose r hr hoff using hsep
  have ht (p : S) : ∃ j : Fin 3, Transcendental K ((Ideal.Quotient.mk p.val) (X j)) :=
    htrans p.val p.property
  choose j hj using ht
  let D : ℕ := S.attach.sup (fun p : S => (r p).totalDegree) + 14
  have hD : 14 ≤ D := by dsimp [D]; omega
  have hrd (p : S) : (r p).totalDegree ≤ D := by
    have h := Finset.le_sup (s := S.attach)
      (f := fun p : S => (r p).totalDegree) (Finset.mem_attach S p)
    dsimp [D]
    omega
  have lower (m : ℕ) : S.card * (m + 1) ≤ Module.finrank K (filteredCoordinateSpace I (D + m)) := by
    have hlin := separated_component_powers_independent I S
      (fun p => ⟨(hS p.val p.property).1.isPrime, (hS p.val p.property).1.le⟩)
      r hr (fun p q hpq => hoff q p.val p.property (fun h => hpq (Subtype.ext h))) j hj m
    have hmem (t : S × Fin (m + 1)) :
        (Ideal.Quotient.mk I) (r t.1 * X (j t.1) ^ t.2.val) ∈
          filteredCoordinateSpace I (D + m) := by
      apply Submodule.mem_map.mpr
      refine ⟨r t.1 * X (j t.1) ^ t.2.val, ?_, rfl⟩
      rw [mem_restrictTotalDegree]
      apply (totalDegree_mul _ _).trans
      rw [totalDegree_X_pow]
      have ht := t.2.isLt
      have hd := hrd t.1
      omega
    let v : S × Fin (m + 1) → filteredCoordinateSpace I (D + m) :=
      fun t => ⟨(Ideal.Quotient.mk I) (r t.1 * X (j t.1) ^ t.2.val), hmem t⟩
    have hv : LinearIndependent K v :=
      LinearIndependent.of_comp (filteredCoordinateSpace I (D + m)).subtype hlin
    simpa using hv.fintype_card_le_finrank
  let m := C * (D + 2)
  have hlo := lower m
  have hhi := hbound (D + m) (by omega)
  dsimp [m] at hlo hhi
  nlinarith


/-- A linear filtered-space bound controls the number of height-two minimal primes. -/
theorem minimalPrime_card_le_of_filtered_bound {K : Type*} [Field K] [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin 3) K)) (S : Finset (Ideal (MvPolynomial (Fin 3) K)))
    (hS : ∀ p ∈ S, p ∈ I.minimalPrimes ∧ p.height = 2)
    (C : ℕ) (hbound : ∀ N, 14 ≤ N → Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 2)) :
    S.card ≤ C := by
  apply minimalPrime_card_le_of_transcendental_coordinates I S hS _ C hbound
  intro p hp
  let : p.IsPrime := (hS p hp).1.isPrime
  exact height_two_has_transcendental_coordinate p (hS p hp).2


/-- At most twenty-four prime components suffice for the actual fixed-dividend
intersection. The bound is proved directly from filtered dimensions. -/
theorem curve_finite_prime_decomposition_le_twenty_four {ρ u v : ℝ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) (ρ' u' v' A a : ℂ) (ha : a ≠ 0) :
    ∃ S : Finset (Ideal (MvPolynomial (Fin 3) ℂ)), S.card ≤ 24 ∧
      (∀ p ∈ S, p.IsPrime ∧ p.height = 2) ∧
      (∀ x, (MvPolynomial.eval x (curveQuadratic (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v') = 0 ∧
        MvPolynomial.eval x (curveEquation (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' A a) = 0) ↔
        ∃ p ∈ S, x ∈ coordinateZeroLocus p) := by
  classical
  let f := curveQuadratic (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v'
  let g := curveEquation (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' A a
  let I : Ideal (MvPolynomial (Fin 3) ℂ) := Ideal.span {f, g}
  have hf : Prime f := by
    apply Irreducible.prime
    apply lineQuadratic_irreducible
    all_goals exact_mod_cast (by linarith : _ ≠ (0 : ℝ))
  have hfg : ¬ f ∣ g := curveQuadratic_not_dvd_fixed_dividend hρ hu hv ρ' u' v' A a ha
  let hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin 3) ℂ) I
  let S := hfin.toFinset
  have hS (p : Ideal (MvPolynomial (Fin 3) ℂ)) (hp : p ∈ S) :
      p ∈ I.minimalPrimes ∧ p.height = 2 := by
    have hp' := hfin.mem_toFinset.mp hp
    exact ⟨hp', minimalPrime_pair_height_two hf hfg hp'⟩
  refine ⟨S, ?_, ?_, ?_⟩
  · apply minimalPrime_card_le_of_filtered_bound I S hS 24
    intro N hN
    exact curve_filteredCoordinateSpace_le hρ hu hv ρ' u' v' A a ha I
      (Ideal.subset_span (by simp : f ∈ ({f, g} : Set (MvPolynomial (Fin 3) ℂ))))
      (Ideal.subset_span (by simp : g ∈ ({f, g} : Set (MvPolynomial (Fin 3) ℂ)))) hN
  · intro p hp
    exact ⟨(hS p hp).1.isPrime, (hS p hp).2⟩
  · intro x
    simpa only [S, hfin.mem_toFinset] using common_zero_iff_minimalPrime f g x

end
end PierceLengthBound.FixedDividend
