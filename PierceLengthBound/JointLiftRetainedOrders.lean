/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ChartNewtonOrders
public import PierceLengthBound.ChartRawDeterminantOrders
public import PierceLengthBound.JointLiftRetainedIdentities

/-! Quotient and rank-three orders on retained components. The normalization
and resolvent equations are ideal membership hypotheses; all determinant and
coefficient orders are derived from the actual component and its chart. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma map_jointGapPolynomials {F : Type*} [Field F] [Algebra ℚ F]
    (ψ : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] F) (a b i : ℕ) (j : Fin 5) :
    ψ (jointGapPolynomials a b i j) =
      lineGaps (algebraMap ℚ F (patternRhoQ a b i))
        (algebraMap ℚ F (patternUQ a b i)) (algebraMap ℚ F (patternVQ a b i))
        (algebraMap ℚ F (patternRhoQ a b (i + 1)))
        (algebraMap ℚ F (patternUQ a b (i + 1)))
        (algebraMap ℚ F (patternVQ a b (i + 1))) (ψ (X 0)) (ψ (X 1)) (ψ (X 2)) j := by
  change ψ.toRingHom (lineGaps _ _ _ _ _ _ _ _ _ j) = _
  rw [map_lineGaps]
  have hc (c : ℚ) : ψ.toRingHom (C c) = algebraMap ℚ F c := ψ.commutes c
  rw [hc, hc, hc, hc, hc, hc]
  rfl

/-- On every retained nonexceptional component through an actual supported
point, the infinity multiplicity is even, q has order -3t, and I3 has order 3t.
This statement assumes neither determinant orders nor coefficient bounds. -/
theorem retained_quotient_and_rank_three_discrete_orders
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
    ∃ t : ℤ, 0 < t ∧ e = 2 * t ∧
      ν (ψ (orbitQuotientNumeratorQ a b i) / ψ (orbitQuotientDenominatorQ a b i)) =
        ((-3 * t : ℤ) : WithTop ℤ) ∧
      ν (ψ (orbitLiftNumeratorQ a b i) / ψ (orbitLiftDenominatorQ a b i)) =
        ((3 * t : ℤ) : WithTop ℤ) := by
  let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
  let q := ψ (orbitQuotientNumeratorQ a b i) / ψ (orbitQuotientDenominatorQ a b i)
  let E := ψ (orbitLiftNumeratorQ a b i) / ψ (orbitLiftDenominatorQ a b i)
  let k := fun j => ψ (jointGapPolynomials a b i j)
  let c := fun j : Fin 4 => coeffs (patternRhoQ a b i) (patternUQ a b i)
    (patternVQ a b i) j.castSucc
  let p := (firstNewtonQuartic (fun j => ψ (C (c j)))
    ![ψ (X 0), ψ (X 1), ψ (X 2), 0]).eval (-q)
  have hzero (f : MvPolynomial (Fin 3) ℚ) (hf : f ∈ I) : ψ f = 0 := by
    change ι (Ideal.Quotient.mk I f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  obtain ⟨hden, hQ⟩ := orbit_reconstruction_field_denominators hba hi I hx ι hι
  have hn : ψ (C (Lz a b i : ℚ)) * p =
      ψ (C (a : ℚ)) * muH4 (k 0) (k 1) (k 2) (k 3) (k 4) :=
    jointNormalizationPolynomial_field_identity ψ a b i hden (hzero _ hnorm)
  have hr : E * p = ψ (C (a : ℚ)) * ((q - ψ (jointQuarticCubicCoefficient a b i)) *
      rawHankelThree (k 0) (k 1) (k 2) - rawHankelMixed (k 0) (k 1) (k 2) (k 3)) :=
    jointResolventPolynomial_field_identity ψ a b i hden hQ (hzero _ hres)
  have hc (r : ℚ) : ψ (C r) = algebraMap ℚ F r := ψ.commutes r
  have hconst (r : ℚ) (hr : r ≠ 0) : ν (ψ (C r)) = 0 := by
    rw [hc]
    exact chart_constant_discrete_order _ ν hregular hr
  obtain ⟨hρ, hu, hv, hne', ha, hA⟩ := orbit_rational_nonexceptional_data hba hi hne
  have hdet := nonexceptional_raw_determinant_discrete_orders hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι hd hdegree ν hregular he hw
  have hψ (f : MvPolynomial (Fin 3) ℚ) : ψ f = ι (Ideal.Quotient.mk I f) := rfl
  have hk (j : Fin 5) := map_jointGapPolynomials ψ a b i j
  have hB : ν (rawHankelThree (k 0) (k 1) (k 2)) = ((-3 * e : ℤ) : WithTop ℤ) := by
    simpa only [k, hk, hψ] using hdet.1
  have hH : ν (muH4 (k 0) (k 1) (k 2) (k 3) (k 4)) = ((-6 * e : ℤ) : WithTop ℤ) := by
    simpa only [k, hk, hψ] using hdet.2.2
  have hp : ν p = ((-6 * e : ℤ) : WithTop ℤ) := by
    have hh := congrArg ν hn
    simpa only [ν.map_mul, hconst _ hA, hconst _ ha, zero_add, hH] using hh
  have hl : ι (Ideal.Quotient.mk I (X 0)) ≠ 0 := by
    intro hz
    rw [hz, inv_zero, ν.map_zero] at hw
    exact WithTop.top_ne_coe hw
  obtain ⟨t, ht, het, hq⟩ := chart_newton_quotient_discrete_order I ι _ hl ν hregular he hw c q
    (by simpa only [p, hc, hψ] using hp)
  have hp3 := chart_polynomial_discrete_order_ge I ι _ hl ν hregular hw
    (jointQuarticCubicCoefficient a b i) 1 (jointQuarticCubicCoefficient_degree a b i)
  have hM := chart_polynomial_discrete_order_ge I ι _ hl ν hregular hw
    (rawHankelMixed (jointGapPolynomials a b i 0) (jointGapPolynomials a b i 1)
      (jointGapPolynomials a b i 2) (jointGapPolynomials a b i 3)) 4
    (rawHankelMixed_totalDegree _ (jointGapPolynomials_degree a b i))
  change ((-4 * e : ℤ) : WithTop ℤ) ≤ ν (ψ.toRingHom (rawHankelMixed _ _ _ _)) at hM
  rw [map_rawHankelMixed] at hM
  change ((-4 * e : ℤ) : WithTop ℤ) ≤ ν (rawHankelMixed (k 0) (k 1) (k 2) (k 3)) at hM
  simp only [Nat.cast_one, neg_one_mul] at hp3
  change ((-e : ℤ) : WithTop ℤ) ≤ ν (ψ (jointQuarticCubicCoefficient a b i)) at hp3
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz, ν.map_zero] at hp
    exact WithTop.top_ne_coe hp
  have hE : E = ψ (C (a : ℚ)) * ((q - ψ (jointQuarticCubicCoefficient a b i)) *
      rawHankelThree (k 0) (k 1) (k 2) - rawHankelMixed (k 0) (k 1) (k 2) (k 3)) / p :=
    (eq_div_iff hp0).mpr hr
  refine ⟨t, ht, het, hq, ?_⟩
  change ν E = _
  rw [hE]
  apply resolvent_discrete_order ν ht (hconst _ ha) hq
  · simpa only [show -e = -2 * t by omega] using hp3
  · simpa only [show -3 * e = -6 * t by omega] using hB
  · simpa only [show -4 * e = -8 * t by omega] using hM
  · simpa only [show -6 * e = -12 * t by omega] using hp

end
end PierceLengthBound.FixedDividend
