/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftConicProperness
public import PierceLengthBound.FixedDividendConicPolynomialIdentities
public import PierceLengthBound.FixedDividendOrbitConicParameter

/-! Lemmas A.1 and A.2 (`lem:jointconicparameter`, `lem:jointconicproper`) for the orbit: a
degree-two component of a nonexceptional pattern curve in a bounded integer plane, carrying the
free nodes of more than `492` orbit states with the same `θ`, has a bounded integral parameter
along which the integral lift is strictly proper. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- The free nodes `q_{i+j+1} - q_i`, `j < 3`, of an orbit state as integers. -/
def orbitFreeNodesZ (a b i : ℕ) : Fin 3 → ℤ :=
  fun j => (qq a b (i + (j.val + 1)) : ℤ) - qq a b i

lemma orbitFreeNodesZ_cast (a b i : ℕ) :
    (fun j => (orbitFreeNodesZ a b i j : ℚ)) = orbitFreeNodesQ a b i := by
  funext j
  simp [orbitFreeNodesZ, orbitFreeNodesQ]

/-- Let the pattern at `i` be nonexceptional and let `I` be a degree-two prime component of
the pattern curve through the free nodes at `i`, contained in an integer plane of height at most
`L`, whose zero locus contains the distinct free nodes of more than `492` states with the same
`θ`. Then there is a coordinate permutation `σ`, a common denominator `E ≠ 0` and quadratic
integer numerators `F` with the explicit heights of `orbit_bounded_integer_parameter`, giving an
injective integer parameter on the integer points of `I`, and along `normalizedParameter σ E F`
the lift has reduced denominator of degree three more than its numerator, positive and at most
twelve. -/
theorem orbit_bounded_integer_parameter_proper {a b i : ℕ} (hba : b < a)
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
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    {ι : Type*} [Fintype ι] (l : ι → ℕ)
    (hl : ∀ j, l j + 7 < P a b) (hθ : ∀ j, theta a b i = theta a b (l j))
    (hpoints : ∀ j, orbitFreeNodesQ a b (l j) ∈ coordinateZeroLocus I)
    (hinj : Function.Injective (fun j => orbitFreeNodesQ a b (l j)))
    (hcard : 492 < Fintype.card ι) :
    ∃ (σ : Fin 3 ≃ Fin 3) (v : Fin 6 → ℤ) (E : ℤ) (F : Fin 3 → Polynomial ℤ),
      σ 1 = 0 ∧ E ≠ 0 ∧
      (∀ j, |v j| ≤ 10 * (12 * (X : ℤ) ^ 4) ^ 2 * L ^ 2) ∧
      |E| ≤ 12 * (L : ℤ) * (10 * (12 * X ^ 4) ^ 2 * L ^ 2) ^ 3 ∧
      (∀ j, (F j).natDegree ≤ 2) ∧
      (∀ j k, |(F j).coeff k| ≤ 33 * (L : ℤ) * (10 * (12 * X ^ 4) ^ 2 * L ^ 2) ^ 3) ∧
      (∀ w : Fin 3 → ℤ, (fun j => (w j : ℚ)) ∈ coordinateZeroLocus I →
        ∀ j, E * w (σ j) = (F j).eval (2 * v 0 * w (σ 0) + v 1 * w (σ 1) + v 3)) ∧
      Set.InjOn (fun w : Fin 3 → ℤ => 2 * v 0 * w (σ 0) + v 1 * w (σ 1) + v 3)
        {w | (fun j => (w j : ℚ)) ∈ coordinateZeroLocus I} ∧
      (orbitLiftParameter a b i (normalizedParameter σ E F)).num.natDegree + 3 =
        (orbitLiftParameter a b i (normalizedParameter σ E F)).denom.natDegree ∧
      0 < (orbitLiftParameter a b i (normalizedParameter σ E F)).denom.natDegree ∧
      (orbitLiftParameter a b i (normalizedParameter σ E F)).denom.natDegree ≤ 12 := by
  classical
  obtain ⟨σ, v, E, F, hσ, hE, hvb, hEb, hFd, hFb, hF2, hrepr, hp_inj⟩ :=
    orbit_bounded_integer_parameter hba hi hX hL ht hne I hf hg n e hn hnb heb hplane hdegree hx
  let p : (Fin 3 → ℤ) → ℤ := fun w => 2 * v 0 * w (σ 0) + v 1 * w (σ 1) + v 3
  let z := normalizedParameter σ E F
  have hZ : ∀ j, (fun k => (orbitFreeNodesZ a b (l j) k : ℚ)) ∈ coordinateZeroLocus I := by
    intro j
    rw [orbitFreeNodesZ_cast]
    exact hpoints j
  have hZinj : Function.Injective (fun j => orbitFreeNodesZ a b (l j)) := by
    intro j k hjk
    dsimp only at hjk
    apply hinj
    change orbitFreeNodesQ a b (l j) = orbitFreeNodesQ a b (l k)
    rw [← orbitFreeNodesZ_cast a b (l j), ← orbitFreeNodesZ_cast a b (l k), hjk]
  let S : Finset (Fin 3 → ℤ) := Finset.univ.image (fun j => orbitFreeNodesZ a b (l j))
  have hS : ∀ w ∈ S, (fun j => (w j : ℚ)) ∈ coordinateZeroLocus I := by
    intro w hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    exact hZ j
  have hScard : S.card = Fintype.card ι := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ hZinj, Finset.card_univ]
  have hident := normalizedParameter_curve_identities
    (patternRhoQ a b i) (patternUQ a b i) (patternVQ a b i)
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i) a I hf hg σ hE F hFd p hrepr hp_inj S hS (by omega)
  have hzeval (w : Fin 3 → ℤ) (hw : (fun j => (w j : ℚ)) ∈ coordinateZeroLocus I) :
      ∀ j, (z j).eval (p w : ℚ) = (w j : ℚ) :=
    normalizedParameter_eval σ hE F w (p w) (hrepr w hw)
  let t : ι → ℚ := fun j => (p (orbitFreeNodesZ a b (l j)) : ℚ)
  have ht_inj : Function.Injective t := by
    intro j k hjk
    apply hZinj
    apply hp_inj (hZ j) (hZ k)
    dsimp only [t] at hjk
    exact_mod_cast hjk
  have hp : ∀ j k, (z k).eval (t j) = orbitFreeNodesQ a b (l j) k := by
    intro j k
    have he := hzeval (orbitFreeNodesZ a b (l j)) (hZ j) k
    exact he.trans (congrFun (orbitFreeNodesZ_cast a b (l j)) k)
  have hz0 : ∀ j, (z j).eval (p (orbitFreeNodesZ a b i) : ℚ) = orbitFreeNodesQ a b i j := by
    intro j
    have hxZ : (fun k => (orbitFreeNodesZ a b i k : ℚ)) ∈ coordinateZeroLocus I := by
      rw [orbitFreeNodesZ_cast]; exact hx
    exact (hzeval _ hxZ j).trans (congrFun (orbitFreeNodesZ_cast a b i) j)
  have hproper := orbit_conic_integralLift_proper hba hi hne z
    (normalizedParameter_degree σ E F hFd) (normalizedParameter_first_coeff σ hσ hE F hF2)
    hident.1 hident.2 (p (orbitFreeNodesZ a b i) : ℚ) hz0 l t ht_inj hl hθ hp hcard
  exact ⟨σ, v, E, F, hσ, hE, hvb, hEb, hFd, hFb, hrepr, hp_inj, hproper.1, hproper.2.1, hproper.2.2⟩

end
end PierceLengthBound.FixedDividend
