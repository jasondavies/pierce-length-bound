/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import PierceLengthBound.RationalNeighborhoodJet
public import PierceLengthBound.PolarProjectionCertificateSection
public import PierceLengthBound.PolarProjectionCurveInitial
public import PierceLengthBound.PolarProjectionFormalSection
public import PierceLengthBound.HypersurfacePatternChart

/-! A fixed exceptional polynomial for the polar base point: one proper
polynomial in the ten full minor coordinates whose nonvanishing gives the chart
guard and a nonzero initial minor. Properness comes from the rational
certificate `(2, 5, -3, 3, 6, -5)`, realized on the minor cone by an explicit
matrix, and the `RationalNear` calculus that clears denominators. -/
@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial Matrix MvPolynomial
noncomputable section

/-- The rational pattern parameters `(ρ, u, v, ρ', u', v')` of the certificate, at which the
initial minor `polarInitialMinor` is nonzero. -/
def polarParameterCertificate : Fin 6 → ℚ := ![2, 5, -3, 3, 6, -5]

/-- The straight formal path of node gaps through the polar base point, with first-order
term the tangent direction `(s, t)`. -/
def polarStraightGapPath (q : Fin 6 → ℚ) (s t : ℚ) (j : Fin 3) : PowerSeries ℚ :=
  PowerSeries.C (polarBaseGaps (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) j) +
    PowerSeries.C (polarTangentDirection (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) s t j) *
      PowerSeries.X

/-- The first-order coefficients of the four remainder monomial coefficients along the straight
gap path. -/
def polarInitialRemainder (q : Fin 6 → ℚ) (s t : ℚ) : Fin 4 → ℚ :=
  let x := polarStraightGapPath q s t
  let nodes := completeNodes (PowerSeries.C (q 0)) (PowerSeries.C (q 1)) (PowerSeries.C (q 2))
    ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
  fun j => PowerSeries.coeff 1 (polarRemainderMonomialCoeffs
    (PowerSeries.C (q 0)) (PowerSeries.C (q 1)) (PowerSeries.C (q 2))
    (PowerSeries.C (q 3)) (PowerSeries.C (q 4)) (PowerSeries.C (q 5)) nodes j)

/-- The first-order coefficient of the cubic line norm along the straight gap path. -/
def polarInitialNorm (q : Fin 6 → ℚ) (s t : ℚ) : ℚ :=
  let x := polarStraightGapPath q s t
  PowerSeries.coeff 1 (lineNorm
    (PowerSeries.C (q 0)) (PowerSeries.C (q 1)) (PowerSeries.C (q 2))
    (PowerSeries.C (q 3)) (PowerSeries.C (q 4)) (PowerSeries.C (q 5))
    (x 0) (x 0 + x 1) (x 0 + x 1 + x 2))

/-- The resultant of the base Newton quartic and the cubic of the first-order remainder along the
tangent direction `(s, t)`. -/
def polarInitialResultant (q : Fin 6 → ℚ) (s t : ℚ) : ℚ :=
  resultant (firstNewtonQuartic (fun j : Fin 4 => coeffs (q 0) (q 1) (q 2) j.castSucc)
    (polarBaseNodes (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)))
    (polarCubic (polarInitialRemainder q s t)) 4 4

/-- The `2 × 2` minor of the initial forms on the two coordinate axes `(1, 0)` and `(0, 1)`. Its
nonvanishing makes the quartic initial coefficient `A R - b N⁴` nonzero on one of the axes. -/
def polarInitialMinor (q : Fin 6 → ℚ) : ℚ :=
  polarInitialResultant q 1 0 * polarInitialNorm q 0 1 ^ 4 -
    polarInitialResultant q 0 1 * polarInitialNorm q 1 0 ^ 4

/-- Split a `RationalNear` goal along the field operations down to coordinates, constants and
the leaf facts `hs`; the nonvanishing side goals of divisions are closed by `norm_num [ns]`. -/
local macro "rational_near" " [" hs:term,* "]" " [" ns:term,* "]" : tactic => do
  let leaf ← hs.getElems.foldrM (fun h acc => `(tactic| first | exact $h | $acc:tactic))
    (← `(tactic| fail))
  `(tactic| repeat' first
    | exact RationalNear.coordinate _
    | exact RationalNear.constant _
    | $leaf:tactic
    | apply RationalNear.div
    | apply RationalNear.add
    | apply RationalNear.sub
    | apply RationalNear.neg
    | apply RationalNear.mul
    | norm_num [$[$ns:term],*])

private lemma rational_base_nodes (j : Fin 4) :
    RationalNear polarParameterCertificate
      (fun q => polarBaseNodes (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) j) := by
  fin_cases j <;> simp only [polarBaseNodes] <;> rational_near [] [polarParameterCertificate]

private lemma rational_base_gaps (j : Fin 3) :
    RationalNear polarParameterCertificate
      (fun q => polarBaseGaps (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) j) := by
  fin_cases j <;> simp only [polarBaseGaps]
  · exact rational_base_nodes 0
  · exact (rational_base_nodes 1).sub (rational_base_nodes 0)
  · exact (rational_base_nodes 2).sub (rational_base_nodes 1)

private lemma rational_tangent (s t : ℚ) (j : Fin 3) :
    RationalNear polarParameterCertificate
      (fun q => polarTangentDirection (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) s t j) := by
  fin_cases j <;> simp only [polarTangentDirection, polarLinear,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  all_goals rational_near [] [polarParameterCertificate]

private lemma rational_path (s t : ℚ) (j : Fin 3) :
    RationalFirstJet polarParameterCertificate (fun q => polarStraightGapPath q s t j) :=
  (RationalFirstJet.C (rational_base_gaps j)).add
    ((RationalFirstJet.C (rational_tangent s t j)).mul (RationalFirstJet.constant _))

/-- The nine power series substituted into the universal remainder and norm polynomials. -/
private def polarJetInputs (s t : ℚ) (q : Fin 6 → ℚ) : Fin 9 → PowerSeries ℚ :=
  ![PowerSeries.C (q 0), PowerSeries.C (q 1), PowerSeries.C (q 2),
    PowerSeries.C (q 3), PowerSeries.C (q 4), PowerSeries.C (q 5),
    polarStraightGapPath q s t 0,
    polarStraightGapPath q s t 0 + polarStraightGapPath q s t 1,
    polarStraightGapPath q s t 0 + polarStraightGapPath q s t 1 + polarStraightGapPath q s t 2]

private lemma rational_jet_inputs (s t : ℚ) (j : Fin 9) :
    RationalFirstJet polarParameterCertificate (fun q => polarJetInputs s t q j) := by
  fin_cases j
  all_goals first
    | exact RationalFirstJet.C (RationalNear.coordinate _)
    | exact rational_path s t _
    | exact (rational_path s t 0).add (rational_path s t 1)
    | exact ((rational_path s t 0).add (rational_path s t 1)).add (rational_path s t 2)

/-- The remainder coefficients are a fixed polynomial in the nine jet inputs. -/
private lemma rational_remainder (s t : ℚ) (j : Fin 4) :
    RationalNear polarParameterCertificate (fun q => polarInitialRemainder q s t j) := by
  have h := RationalFirstJet.polynomial
    (polarRemainderMonomialCoeffs (X (0 : Fin 9)) (X 1) (X 2) (X 3) (X 4) (X 5)
      (completeNodes (X 0) (X 1) (X 2) ![X 6, X 7, X 8]) j)
    (polarJetInputs s t) (rational_jet_inputs s t)
  simp only [map_polarRemainderMonomialCoeffs, map_completeNodes, MvPolynomial.eval₂Hom_X'] at h
  convert h.2 using 2 with q
  simp only [polarInitialRemainder, completeNodes, polarJetInputs, Matrix.cons_val,
    MvPolynomial.eval₂Hom_X']

private lemma rational_norm (s t : ℚ) :
    RationalNear polarParameterCertificate (fun q => polarInitialNorm q s t) := by
  have h := RationalFirstJet.polynomial
    (lineNorm (X (0 : Fin 9)) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6) (X 7) (X 8))
    (polarJetInputs s t) (rational_jet_inputs s t)
  simp only [map_lineNorm, MvPolynomial.eval₂Hom_X'] at h
  exact h.2

private lemma rational_quartic (j : Fin 4) :
    RationalNear polarParameterCertificate (fun q => firstNewtonCoeffs
      (fun j : Fin 4 => coeffs (q 0) (q 1) (q 2) j.castSucc)
      (polarBaseNodes (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)) j) := by
  fin_cases j <;> simp only [firstNewtonCoeffs, coeffs, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Fin.reduceFinMk]
  all_goals rational_near [rational_base_nodes _] []

private lemma rational_resultant (s t : ℚ) :
    RationalNear polarParameterCertificate (fun q => polarInitialResultant q s t) := by
  have he (q : Fin 6 → ℚ) : polarInitialResultant q s t =
      (quarticBezout
        (firstNewtonCoeffs (fun j : Fin 4 => coeffs (q 0) (q 1) (q 2) j.castSucc)
          (polarBaseNodes (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)))
        (firstNewtonCoeffs (fun j : Fin 4 => coeffs (q 0) (q 1) (q 2) j.castSucc)
          (polarBaseNodes (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)) +
            polarInitialRemainder q s t)).det := by
    unfold polarInitialResultant
    rw [firstNewtonQuartic_eq, polarCubic_resultant]
  simp_rw [he]
  apply RationalNear.det
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [quarticBezout, Pi.add_apply]
  all_goals rational_near [rational_quartic _, rational_remainder s t _] []

/-- The initial minor is a rational function regular at the certificate parameters. -/
theorem polar_initial_minor_rational : RationalNear polarParameterCertificate polarInitialMinor :=
  ((rational_resultant 1 0).mul ((rational_norm 0 1).pow 4)).sub
    ((rational_resultant 0 1).mul ((rational_norm 1 0).pow 4))

private lemma straight_certificate_zero (s t : ℚ) (j : Fin 3) :
    PowerSeries.constantCoeff (polarStraightGapPath polarParameterCertificate s t j) =
      ![-1 / 7, -3 / 28, -1 / 2] j := by
  fin_cases j <;> norm_num [polarStraightGapPath, polarParameterCertificate,
    polarBaseGaps, polarBaseNodes]

private lemma straight_certificate_one (s t : ℚ) (j : Fin 3) :
    PowerSeries.coeff 1 (polarStraightGapPath polarParameterCertificate s t j) =
      ![(9 * s - 5 * t) / 4, s, t] j := by
  fin_cases j <;> norm_num [polarStraightGapPath, polarParameterCertificate,
    polarTangentDirection, polarLinear]
  ring

lemma polarInitialNorm_certificate (s t : ℚ) :
    polarInitialNorm polarParameterCertificate s t = polarCertificateNormLinear s t := by
  exact polar_certificate_formal_norm_linear _ s t
    (straight_certificate_zero s t) (straight_certificate_one s t)

lemma polarInitialResultant_certificate (s t : ℚ) :
    polarInitialResultant polarParameterCertificate s t = polarCertificateInitialResultant s t := by
  have hr := polar_certificate_formal_remainder_linear
    (polarStraightGapPath polarParameterCertificate s t) s t
    (straight_certificate_zero s t) (straight_certificate_one s t)
  change polarCubic (polarInitialRemainder polarParameterCertificate s t) = _ at hr
  change resultant (firstNewtonQuartic (fun j : Fin 4 => coeffs (2 : ℚ) 5 (-3) j.castSucc)
    (polarBaseNodes (2 : ℚ) 5 (-3) 3 6 (-5))) _ 4 4 = _
  rw [← polarCertificateQuartic_eq_newton, hr]
  rfl

/-- The initial minor at the certificate parameters. -/
theorem polarInitialMinor_certificate :
    polarInitialMinor polarParameterCertificate = 26291112152499 / 60236288 := by
  simpa only [polarInitialMinor, polarInitialResultant_certificate,
    polarInitialNorm_certificate] using polarCertificate_initial_minor

/-- The product of the nonvanishing conditions used to construct the smooth
formal section and its explicit base nodes. -/
def polarChartGuard (q : Fin 6 → ℚ) : ℚ :=
  (-q 0 - q 1) * (q 1 - q 2) * (q 2 - 1) * (polarMatrix (q 0) (q 1) (q 2)).det *
    polarMatrix (q 0) (q 1) (q 2) 0 0 * polarLinear (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) 0

private lemma rational_guard : RationalNear polarParameterCertificate polarChartGuard := by
  change RationalNear polarParameterCertificate (fun q => polarChartGuard q)
  simp only [polarChartGuard, polarMatrix, polarLinear, Matrix.cons_val_zero]
  rational_near [] []

lemma polarChartGuard_certificate : polarChartGuard polarParameterCertificate ≠ 0 := by
  norm_num [polarChartGuard, polarParameterCertificate, polarMatrix, polarLinear,
    Matrix.det_fin_three]

/-- Six normalized coefficients read from the ten full minor coordinates. -/
def polarMinorParameters (p : Fin 10 → ℚ) : Fin 6 → ℚ :=
  ![p 6 / p 0, p 3 / p 0, -p 1 / p 0, p 9 / p 6, p 8 / p 6, -p 7 / p 6]

/-- An explicit matrix realizing the rational certificate on the decomposable cone. -/
def polarMinorCertificateMatrix : Fin 3 → Fin 5 → ℚ :=
  ![![1, 0, 0, 2, 10], ![0, 1, 0, -5, -22], ![0, 0, 1, 3, 9]]

lemma polarMinorCertificate_values :
    plk polarMinorCertificateMatrix = ![1, 3, 9, 5, 22, 21, 2, 10, 12, 6] := by
  ext j
  fin_cases j <;> norm_num [plk, minor3, trip, polarMinorCertificateMatrix]

lemma polarMinorParameters_certificate :
    polarMinorParameters (plk polarMinorCertificateMatrix) = polarParameterCertificate := by
  rw [polarMinorCertificate_values]
  ext j
  fin_cases j <;> norm_num [polarMinorParameters, polarParameterCertificate]

private lemma rational_minor_parameters (j : Fin 6) :
    RationalNear (plk polarMinorCertificateMatrix) (fun p => polarMinorParameters p j) := by
  fin_cases j <;> simp only [polarMinorParameters] <;>
    rational_near [] [polarMinorCertificate_values]

/-- The exceptional condition is one fixed proper polynomial in the full
minor vector. Outside its zero locus, `p 0` and `p 6` are nonzero and the
normalized parameters satisfy the chart guard and have a nonzero initial minor. -/
theorem exists_polar_full_minor_exceptional_polynomial :
    ∃ Θ : MvPolynomial (Fin 10) ℚ, ProperOnMinorCone Θ ∧
      ∀ p, eval p Θ ≠ 0 → p 0 ≠ 0 ∧ p 6 ≠ 0 ∧
        polarChartGuard (polarMinorParameters p) ≠ 0 ∧
        polarInitialMinor (polarMinorParameters p) ≠ 0 := by
  have hr := (rational_guard.mul polar_initial_minor_rational).comp
    polarMinorParameters rational_minor_parameters polarMinorParameters_certificate
  have hc : (plk polarMinorCertificateMatrix 0 * plk polarMinorCertificateMatrix 6) *
      (polarChartGuard (polarMinorParameters (plk polarMinorCertificateMatrix)) *
        polarInitialMinor (polarMinorParameters (plk polarMinorCertificateMatrix))) ≠ 0 := by
    rw [polarMinorParameters_certificate]
    exact mul_ne_zero (by norm_num [polarMinorCertificate_values])
      (mul_ne_zero polarChartGuard_certificate (by rw [polarInitialMinor_certificate]; norm_num))
  obtain ⟨Θ, hΘ, hgood⟩ := ((RationalNear.coordinate 0).mul (RationalNear.coordinate 6)).mul hr
    |>.exists_nonvanishing_polynomial hc
  refine ⟨Θ, ⟨polarMinorCertificateMatrix, hΘ⟩, ?_⟩
  intro p hp
  obtain ⟨hcoords, hg⟩ := mul_ne_zero_iff.mp (hgood p hp)
  exact ⟨(mul_ne_zero_iff.mp hcoords).1, (mul_ne_zero_iff.mp hcoords).2,
    (mul_ne_zero_iff.mp hg).1, (mul_ne_zero_iff.mp hg).2⟩

end
end PierceLengthBound.FixedDividend
