/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ChartFiniteOverParameter
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental

/-! The infinity coordinate is a genuine transcendental parameter. Its
algebraicity would make the finite chart a finite-dimensional constant algebra,
contradicting the positive slope of the original affine Hilbert function. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

theorem chartInfinityCoordinate_transcendental {K σ F : Type*}
    [Field K] [Field F] [Algebra K F] [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hι : Function.Injective ι)
    (l : MvPolynomial σ K ⧸ I) (hl : l ∈ filteredCoordinateSpace I 1) (hl0 : ι l ≠ 0)
    {d N M : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (hspan : ∀ n ≥ M, filteredCoordinateSpace I (n + 1) ⊔
      (filteredCoordinateSpace I (n + 1)).map (LinearMap.mulLeft K l) =
        filteredCoordinateSpace I (n + 2)) :
    Transcendental K (chartInfinityCoordinate I ι l) := by
  intro hw
  let S := projectiveChart I ι l
  let T := Algebra.adjoin K {chartInfinityCoordinate I ι l}
  let : Module.Finite K T := Algebra.finite_adjoin_simple_of_isIntegral hw.isIntegral
  let : Module.Finite T S := projectiveChart_finite_over_parameter I ι l hl hl0 hspan
  let : Module.Finite K S := Module.Finite.trans T S
  have hbound (n : ℕ) : Module.finrank K (filteredCoordinateSpace I n) ≤ Module.finrank K S := by
    apply LinearMap.finrank_le_finrank_of_injective (f := chartMonomialMap I ι l n)
    intro x y hxy
    apply Subtype.ext
    apply hι
    apply mul_right_cancel₀ (pow_ne_zero n (inv_ne_zero hl0))
    exact congrArg (fun z : S => (z : F)) hxy
  obtain ⟨m, hm⟩ := exists_nat_gt ((Module.finrank K S : ℤ) - b)
  let n := max N m
  have hnN : N ≤ n := le_max_left _ _
  have hmn : (m : ℤ) ≤ n := by exact_mod_cast (le_max_right N m)
  have hdn : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hn0 : (0 : ℤ) ≤ n := by positivity
  have hb : (Module.finrank K (filteredCoordinateSpace I n) : ℤ) ≤ Module.finrank K S :=
    by exact_mod_cast hbound n
  rw [hdegree n hnN] at hb
  nlinarith

theorem nonexceptional_chart_parameter_transcendental
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b) :
    Transcendental ℚ (chartInfinityCoordinate I ι (Ideal.Quotient.mk I (MvPolynomial.X 0))) := by
  obtain ⟨M, hs⟩ := rational_nonexceptional_eventual_first_node_generation
    hρ hu hv hne ρ' u' v' A a ha I hf hg
  have hl : ι (Ideal.Quotient.mk I (MvPolynomial.X 0)) ≠ 0 := by
    intro hh
    apply first_node_ne_zero_of_generation I hd hdegree hs
    exact hι (by simpa using hh)
  exact chartInfinityCoordinate_transcendental I ι hι _
    ⟨MvPolynomial.X 0, by simp [MvPolynomial.mem_restrictTotalDegree], rfl⟩ hl hd hdegree hs

end
end PierceLengthBound.FixedDividend
