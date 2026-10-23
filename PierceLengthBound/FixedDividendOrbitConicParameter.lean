/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendConicBoundedModel
public import PierceLengthBound.ConicPlaneHeight
public import PierceLengthBound.ConicParameterHeight

/-!
# Bounded integer parametrization of actual conic components

Actual minor heights give a bounded integral parabolic model at a Pierce orbit
point. A certified integral plane-conic model gives bounded quadratic numerators
for every integral component point and an injective integer parameter, hence a
complete bounded integer parametrization of actual nonexceptional conic points.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Matrix (vec3_dotProduct)
noncomputable section
open MvPolynomial

/-- Actual minor heights give the complete bounded integral conic model.
The only plane input is its integer coefficient bound and actual membership. -/
theorem orbit_bounded_integer_conic_model {a b i : ℕ} (hba : b < a)
    (hi : i + 7 < P a b) {X L : ℤ} (hX : 1 ≤ X) (hL : 0 ≤ L)
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
    ∃ (j k : Fin 3) (v : Fin 6 → ℤ), Function.Bijective ![j, 0, k] ∧ n k ≠ 0 ∧
      (∀ q, |v q| ≤ 10 * (12 * X ^ 4) ^ 2 * L ^ 2) ∧
      v 0 ≠ 0 ∧ (v 1) ^ 2 - 4 * v 0 * v 2 = 0 ∧
      2 * v 1 * v 3 - 4 * v 0 * v 4 ≠ 0 ∧
      ∀ z : Fin 3 → ℤ, (fun q => (z q : ℚ)) ∈ coordinateZeroLocus I →
        conicValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (z j) (z 0) = 0 := by
  let w := conicPatternCommon (theta a b i)
  have hw : ∀ j, |w j| ≤ X ^ 2 := conicPatternCommon_height ht
  have hratio := conicPatternCommon_orbit hba (by omega : i + 6 < P a b)
  have h0 : (w 0 : ℚ) / w 6 = patternRhoQ a b i := congrFun hratio 0
  have h1 : (w 1 : ℚ) / w 6 = patternUQ a b i := congrFun hratio 1
  have h2 : (w 2 : ℚ) / w 6 = patternVQ a b i := congrFun hratio 2
  have h3 : (w 3 : ℚ) / w 6 = patternRhoQ a b (i + 1) := congrFun hratio 3
  have h4 : (w 4 : ℚ) / w 6 = patternUQ a b (i + 1) := congrFun hratio 4
  have h5 : (w 5 : ℚ) / w 6 = patternVQ a b (i + 1) := congrFun hratio 5
  have hL0 : Lz a b i ≠ 0 := ne_of_gt (Lz_pos hba (by omega))
  have hL1 : Lz a b (i + 1) ≠ 0 := ne_of_gt (Lz_pos hba (by omega))
  have hD : w 6 ≠ 0 := mul_ne_zero hL0 hL1
  have hsign := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  have hnormal : n 0 ≠ 0 ∨ n 1 ≠ 0 ∨ n 2 ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hn
    ext j
    fin_cases j <;> simp only [Pi.zero_apply] <;> tauto
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hA : (Lz a b i : ℚ) ≠ 0 := by exact_mod_cast hL0
  have hpEq : integerPlanePolynomial n e = C (n 0 : ℚ) * MvPolynomial.X 0 +
      C (n 1 : ℚ) * MvPolynomial.X 1 + C (n 2 : ℚ) * MvPolynomial.X 2 + C (e : ℚ) := by
    simp only [integerPlanePolynomial, Fin.sum_univ_succ,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring
  rw [hpEq] at hplane
  have hh := nonexceptional_bounded_integer_conic_model
    (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (n 0) (n 1) (n 2) e
    (M := X ^ 2) (by nlinarith) hL hD (hw 0) (hw 1) (hw 2) (hw 3) (hw 4) (hw 5) (hw 6)
    (hnb 0) (hnb 1) (hnb 2) heb
    (by simpa only [h0] using hsign.1) (by simpa only [h1] using hsign.2.1)
    (by simpa only [h2] using hsign.2.2)
    (by simpa only [h0, h1, h2] using nonexceptionalPattern_ratCast hne)
    (Lz a b i) a hA ha I
    (by simpa only [h0, h1, h2, h3, h4, h5, orbitCurveQuadraticQ] using hf)
    (by simpa only [h0, h1, h2, h3, h4, h5, orbitCurveEquationQ] using hg)
    hnormal hplane hdegree (orbitFreeNodesQ a b i) hx
  have he : (![n 0, n 1, n 2] : Fin 3 → ℤ) = n := by ext j; fin_cases j <;> rfl
  simpa only [he, ← pow_mul, Nat.reduceMul] using hh

set_option maxHeartbeats 400000 in
-- This proof uses about 320k heartbeats (`#count_heartbeats`).
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
    have hdot : n ⬝ᵥ z + e = 0 := by exact_mod_cast hh
    have hsum := σ.sum_comp (fun j => n j * z j)
    simp only [Fin.sum_univ_succ,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hsum
    rw [vec3_dotProduct] at hdot
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
