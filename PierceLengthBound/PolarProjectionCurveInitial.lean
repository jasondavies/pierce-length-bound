/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionFirstJet
public import PierceLengthBound.NewtonCoefficientDegrees
public import PierceLengthBound.ChartNodeUnits
public import PierceLengthBound.PolarProjectionInitialForm

/-! The initial coefficient of the original fixed-dividend curve equation
along an arbitrary formal section through the polar base point. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial Matrix
noncomputable section

lemma map_polarRemainderMonomialCoeffs {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (ρ u v ρ' u' v' : R) (s : Fin 4 → R) (j : Fin 4) :
    φ (polarRemainderMonomialCoeffs ρ u v ρ' u' v' s j) =
      polarRemainderMonomialCoeffs (φ ρ) (φ u) (φ v) (φ ρ') (φ u') (φ v')
        (fun k => φ (s k)) j := by
  fin_cases j <;> simp [polarRemainderMonomialCoeffs, polarRemainderCoefficients,
    polarQuotientConstant]

/-- Higher-order corrections to a gap section leave its initial cubic remainder unchanged. -/
theorem polar_formal_remainder_linear_eq_of_jets {K : Type*} [CommRing K]
    (ρ u v ρ' u' v' : K) (x y : Fin 3 → PowerSeries K)
    (hzero : ∀ j, PowerSeries.constantCoeff (x j) = PowerSeries.constantCoeff (y j))
    (hone : ∀ j, PowerSeries.coeff 1 (x j) = PowerSeries.coeff 1 (y j)) (j : Fin 4) :
    PowerSeries.coeff 1 (polarRemainderMonomialCoeffs
      (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
      (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v')
      (completeNodes (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
        ![x 0, x 0 + x 1, x 0 + x 1 + x 2]) j) =
    PowerSeries.coeff 1 (polarRemainderMonomialCoeffs
      (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
      (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v')
      (completeNodes (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
        ![y 0, y 0 + y 1, y 0 + y 1 + y 2]) j) := by
  have hj (k : Fin 3) : formalFirstJet (x k) = formalFirstJet (y k) :=
    TrivSqZeroExt.ext (hzero k) (hone k)
  have hi : (fun k : Fin 3 => formalFirstJet (![x 0, x 0 + x 1, x 0 + x 1 + x 2] k)) =
      fun k : Fin 3 => formalFirstJet (![y 0, y 0 + y 1, y 0 + y 1 + y 2] k) := by
    funext k
    fin_cases k <;> simp [hj]
  change (formalFirstJet _).snd = (formalFirstJet _).snd
  simp only [map_polarRemainderMonomialCoeffs, map_completeNodes, hi]

/-- Higher-order corrections to a gap section leave its norm's linear part unchanged. -/
theorem polar_formal_norm_linear_eq_of_jets {K : Type*} [CommRing K]
    (ρ u v ρ' u' v' : K) (x y : Fin 3 → PowerSeries K)
    (hzero : ∀ j, PowerSeries.constantCoeff (x j) = PowerSeries.constantCoeff (y j))
    (hone : ∀ j, PowerSeries.coeff 1 (x j) = PowerSeries.coeff 1 (y j)) :
    PowerSeries.coeff 1 (lineNorm (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
      (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v')
      (x 0) (x 0 + x 1) (x 0 + x 1 + x 2)) =
    PowerSeries.coeff 1 (lineNorm (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
      (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v')
      (y 0) (y 0 + y 1) (y 0 + y 1 + y 2)) := by
  have hj (k : Fin 3) : formalFirstJet (x k) = formalFirstJet (y k) :=
    TrivSqZeroExt.ext (hzero k) (hone k)
  change (formalFirstJet _).snd = (formalFirstJet _).snd
  simp only [map_lineNorm, map_add, hj]

/-- The explicit resultant formula is the quartic initial form of the
original curve equation, on every formal path through the base point. -/
theorem polar_curve_formal_initial {K : Type*} [Field K]
    (ρ u v ρ' u' v' A b : K) (hG : (polarMatrix ρ u v).det ≠ 0)
    (h1 : -ρ - u ≠ 0) (h2 : u - v ≠ 0) (h3 : v - 1 ≠ 0)
    (x : Fin 3 → PowerSeries K)
    (hx : ∀ j, PowerSeries.constantCoeff (x j) = polarBasePoint ρ u v ρ' u' v' j) :
    let z : Fin 3 → PowerSeries K := ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
    let nodes := completeNodes (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v) z
    let rem := polarRemainderMonomialCoeffs
      (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
      (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v') nodes
    let D := lineNorm (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
      (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v') (z 0) (z 1) (z 2)
    let E := MvPolynomial.eval z (curveEquation
      (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
      (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v') (PowerSeries.C A) (PowerSeries.C b))
    (∀ k < 4, PowerSeries.coeff k E = 0) ∧
      PowerSeries.coeff 4 E =
        A * resultant (firstNewtonQuartic (fun j : Fin 4 => coeffs ρ u v j.castSucc)
          (polarBaseNodes ρ u v ρ' u' v'))
            (polarCubic (fun j => PowerSeries.coeff 1 (rem j))) 4 4 -
          b * PowerSeries.coeff 1 D ^ 4 := by
  dsimp only
  let z : Fin 3 → PowerSeries K := ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
  let nodes := completeNodes (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v) z
  let rem := polarRemainderMonomialCoeffs
    (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
    (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v') nodes
  let aa := firstNewtonCoeffs
    (fun j : Fin 4 => coeffs (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v) j.castSucc) nodes
  let D := lineNorm (PowerSeries.C ρ) (PowerSeries.C u) (PowerSeries.C v)
    (PowerSeries.C ρ') (PowerSeries.C u') (PowerSeries.C v') (z 0) (z 1) (z 2)
  have hz : (fun j => PowerSeries.constantCoeff (z j)) =
      fun j : Fin 3 => polarBaseNodes ρ u v ρ' u' v' j.castSucc := by
    funext j
    fin_cases j <;>
      simp [z, hx, ← polarBaseGaps_eq_basePoint ρ u v ρ' u' v' hG h1 h2 h3, polarBaseGaps]
  have hn : (fun j => PowerSeries.constantCoeff (nodes j)) =
      polarBaseNodes ρ u v ρ' u' v' := by
    funext j
    rw [show PowerSeries.constantCoeff (nodes j) =
      completeNodes ρ u v (fun k => PowerSeries.constantCoeff (z k)) j by
        simp [nodes, map_completeNodes], hz,
      polarBaseNodes_completeNodes ρ u v ρ' u' v' h1 h2 h3]
  have hr : ∀ j, PowerSeries.constantCoeff (rem j) = 0 := by
    intro j
    simp only [rem, map_polarRemainderMonomialCoeffs, PowerSeries.constantCoeff_C, hn]
    fin_cases j <;>
      simp [polarRemainderMonomialCoeffs,
        polarBaseNodes_remainderCoefficients ρ u v ρ' u' v' h1 h2 h3]
  have hD : PowerSeries.constantCoeff D = 0 := by
    have he := polarBasePoint_norm_zero ρ u v ρ' u' v' hG
    simpa [D, z, map_lineNorm, hx] using he
  have haa : (fun j => PowerSeries.constantCoeff (aa j)) =
      firstNewtonCoeffs (fun j : Fin 4 => coeffs ρ u v j.castSucc)
        (polarBaseNodes ρ u v ρ' u' v') := by
    funext j
    simp only [aa, map_firstNewtonCoeffs, hn]
    congr 2
    funext k
    fin_cases k <;> simp [coeffs]
  have he := polar_equation_initial_form aa rem D A b hr hD
  rw [haa] at he
  simp only [curveEquation, map_sub, map_mul, MvPolynomial.eval_C, map_pow,
    eval_curveNorm, polar_curve_resultant_eq_cubic]
  dsimp only [aa, rem, D, nodes, z] at he
  rw [firstNewtonQuartic_eq]
  simpa only [map_sub] using he

end
end PierceLengthBound.FixedDividend
