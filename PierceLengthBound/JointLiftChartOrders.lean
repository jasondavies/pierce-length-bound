/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftRetainedOrders
public import PierceLengthBound.JointLiftFieldCoordinates
public import PierceLengthBound.JointLiftInfinityOrder

/-! # Orders of the joint coordinates at infinity

Corollary 8.9 of the paper for the four coordinates `W₀, W₁, W₂, J` of the joint graph, at an
arbitrary discrete valuation centered on the infinity chart of a retained nonexceptional
component, including valuations lying above singular points. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- On a retained nonexceptional component, at a discrete valuation centered on the infinity
chart with infinity multiplicity `e`, one has `e = 2t` with `t > 0`, the curvature coordinates
`W₀` and `W₂` have order `3t`, `W₁` has order at least `3t`, and `J` has order `-5t`. -/
theorem retained_joint_coordinates_discrete_orders
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (ν : AddValuation F (WithTop ℤ))
    (hregular : ∀ r : projectiveChart I ι (Ideal.Quotient.mk I (X 0)), 0 ≤ ν (r : F))
    {e : ℤ} (he : 0 < e)
    (hw : ν ((ι (Ideal.Quotient.mk I (X 0)))⁻¹) = (e : WithTop ℤ)) :
    let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
    let W := fun j => ψ (orbitJointNumerators a b i j) / ψ (orbitJointDenominator a b i)
    ∃ t : ℤ, 0 < t ∧ e = 2 * t ∧
      ν (W 0) = ((3 * t : ℤ) : WithTop ℤ) ∧
      ((3 * t : ℤ) : WithTop ℤ) ≤ ν (W 1) ∧
      ν (W 2) = ((3 * t : ℤ) : WithTop ℤ) ∧
      ν (W 3) = ((-5 * t : ℤ) : WithTop ℤ) := by
  let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
  let W := fun j => ψ (orbitJointNumerators a b i j) / ψ (orbitJointDenominator a b i)
  let k := fun j => ψ (jointGapPolynomials a b i j)
  let B0 := rawHankelThree (k 0) (k 1) (k 2)
  let B1 := rawHankelThree (k 1) (k 2) (k 3)
  let E0 := ψ (orbitLiftNumeratorQ a b i) / ψ (orbitLiftDenominatorQ a b i)
  let E12 := (B1 * E0 - ψ (C (Lz a b i : ℚ)) * k 1) / B0
  have hψ (f : MvPolynomial (Fin 3) ℚ) : ψ f = ι (Ideal.Quotient.mk I f) := rfl
  have hD : ψ (orbitJointDenominator a b i) ≠ 0 := by
    intro hz
    exact orbitJoint_denominator_not_mem hba hi I hx
      (Ideal.Quotient.eq_zero_iff_mem.mp (hι (by simpa only [map_zero, hψ] using hz)))
  have hcoordinates : W =
      ![E12, -((k 0 * E12 + k 2 * E0) / k 1), E0, ψ (jointRankFivePolynomial a b i)] :=
    jointLift_field_coordinates ψ.toRingHom _ _ _ _ _ hD
  obtain ⟨t, ht, het, _, hE0⟩ := retained_quotient_and_rank_three_discrete_orders
    hba hi hne I hf hg hx hnorm hres ι hι hd hdegree ν hregular he hw
  obtain ⟨hρ, hu, hv, hne', ha, hA⟩ := orbit_rational_nonexceptional_data hba hi hne
  have hAv : ν (ψ (C (Lz a b i : ℚ))) = 0 := by
    rw [show ψ (C (Lz a b i : ℚ)) = algebraMap ℚ F (Lz a b i : ℚ) from ψ.commutes _]
    exact chart_constant_discrete_order _ ν hregular hA
  have hdet := nonexceptional_raw_determinant_discrete_orders hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι hd hdegree ν hregular he hw
  have hk (j : Fin 5) := map_jointGapPolynomials ψ a b i j
  have hB0 : ν B0 = ((-6 * t : ℤ) : WithTop ℤ) := by
    simpa only [B0, k, hk, hψ, show -3 * e = -6 * t by omega] using hdet.1
  have hB1 : ν B1 = ((-6 * t : ℤ) : WithTop ℤ) := by
    simpa only [B1, k, hk, hψ, show -3 * e = -6 * t by omega] using hdet.2.1
  have hl : ι (Ideal.Quotient.mk I (X 0)) ≠ 0 := by
    intro hz
    rw [hz, inv_zero, ν.map_zero] at hw
    exact WithTop.top_ne_coe hw
  have hkg (j : Fin 5) : ((-2 * t : ℤ) : WithTop ℤ) ≤ ν (k j) := by
    have hh := chart_polynomial_discrete_order_ge I ι _ hl ν hregular hw
      (jointGapPolynomials a b i j) 1 (jointGapPolynomials_degree a b i j)
    simpa only [Nat.cast_one, neg_one_mul, show -e = -2 * t by omega, k, hψ] using hh
  have hk1 : ν (k 1) = ((-2 * t : ℤ) : WithTop ℤ) := by
    have hh := nonexceptional_node_difference_discrete_order hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι hd hdegree ν hregular he hw 2 1 (by decide)
    simpa [k, hk, hψ, lineGaps, completeDirection, show -e = -2 * t by omega] using hh
  have hcurv := curvature_discrete_orders ν ht hAv hB0 hB1 hE0 (hkg 0) hk1 (hkg 2)
  obtain ⟨t', _, het', hJ⟩ := nonexceptional_rank_five_discrete_order hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) hA ha I hf hg ι hι hd hdegree ν hregular he hw
  have htt : t' = t := by omega
  subst t'
  change ∃ t : ℤ, 0 < t ∧ e = 2 * t ∧ ν (W 0) = _ ∧ _ ≤ ν (W 1) ∧
    ν (W 2) = _ ∧ ν (W 3) = _
  refine ⟨t, ht, het, ?_⟩
  rw [hcoordinates]
  exact ⟨hcurv.1, hcurv.2.1, hcurv.2.2, hJ⟩

end
end PierceLengthBound.FixedDividend
