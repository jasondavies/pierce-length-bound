/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftOrbitConicProperness
public import PierceLengthBound.ConicCommonDenominator

/-! A single fixed integer polynomial pair represents every substituted actual
cofactor lift. This makes its uniform coefficient-height control concrete. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial
set_option maxHeartbeats 1000000

/-- Variables zero through five are the two consecutive minor-ratio triples;
six through eight are the free nodes, and nine is the fixed dividend. -/
def universalLiftCofactors : Fin 9 → MvPolynomial (Fin 10) ℤ :=
  momentCofactors (newtonMomentSystem
    (fun j : Fin 4 => coeffs (X 0) (X 1) (X 2) j.castSucc)
    (fun j : Fin 4 => coeffs (X 3) (X 4) (X 5) j.castSucc)
    (completeNodes (X 0) (X 1) (X 2) ![X 6, X 7, X 8]))

def universalLiftNumerator : MvPolynomial (Fin 10) ℤ :=
  cofactorLiftNumerator (X 9) universalLiftCofactors

def universalLiftDenominator : MvPolynomial (Fin 10) ℤ :=
  cofactorLiftDenominator universalLiftCofactors

lemma universalLiftCofactors_eval {R : Type*} [CommRing R] (v : Fin 10 → R) (j : Fin 9) :
    MvPolynomial.eval₂ (Int.castRingHom R) v (universalLiftCofactors j) =
      momentCofactors (newtonMomentSystem
        (fun j : Fin 4 => coeffs (v 0) (v 1) (v 2) j.castSucc)
        (fun j : Fin 4 => coeffs (v 3) (v 4) (v 5) j.castSucc)
        (completeNodes (v 0) (v 1) (v 2) ![v 6, v 7, v 8])) j := by
  change (MvPolynomial.eval₂Hom (Int.castRingHom R) v) (universalLiftCofactors j) = _
  unfold universalLiftCofactors
  rw [map_momentCofactors, map_newtonMomentSystem]
  congr 2
  · funext k
    fin_cases k <;> simp [coeffs]
  · funext k
    fin_cases k <;> simp [coeffs]
  · funext k
    fin_cases k <;> simp [completeNodes, fourthNode]

/-- The ten rational-function inputs for the actual polynomial parameter. -/
def orbitLiftInputs (a b i : ℕ) (z : Fin 3 → Polynomial ℚ) : Fin 10 → RatFunc ℚ :=
  ![algebraMap ℚ (RatFunc ℚ) (patternRhoQ a b i),
    algebraMap ℚ (RatFunc ℚ) (patternUQ a b i),
    algebraMap ℚ (RatFunc ℚ) (patternVQ a b i),
    algebraMap ℚ (RatFunc ℚ) (patternRhoQ a b (i + 1)),
    algebraMap ℚ (RatFunc ℚ) (patternUQ a b (i + 1)),
    algebraMap ℚ (RatFunc ℚ) (patternVQ a b (i + 1)),
    algebraMap (Polynomial ℚ) (RatFunc ℚ) (z 0),
    algebraMap (Polynomial ℚ) (RatFunc ℚ) (z 1),
    algebraMap (Polynomial ℚ) (RatFunc ℚ) (z 2), a]

lemma universalLiftCofactors_orbit (a b i : ℕ) (z : Fin 3 → Polynomial ℚ) (j : Fin 9) :
    MvPolynomial.eval₂ (Int.castRingHom (RatFunc ℚ)) (orbitLiftInputs a b i z)
        (universalLiftCofactors j) =
      algebraMap (Polynomial ℚ) (RatFunc ℚ) (MvPolynomial.aeval z (orbitCurveCofactorsQ a b i j)) := by
  let φ : MvPolynomial (Fin 3) ℚ →+* RatFunc ℚ :=
    (algebraMap (Polynomial ℚ) (RatFunc ℚ)).comp (MvPolynomial.aeval z).toRingHom
  change _ = φ (orbitCurveCofactorsQ a b i j)
  rw [universalLiftCofactors_eval]
  unfold orbitCurveCofactorsQ
  rw [map_momentCofactors]
  unfold curveMomentSystem
  rw [map_newtonMomentSystem]
  congr 2
  · funext k
    fin_cases k <;> simp [orbitLiftInputs, φ, coeffs]
  · funext k
    fin_cases k <;> simp [orbitLiftInputs, φ, coeffs]
  · funext k
    fin_cases k <;> simp [orbitLiftInputs, φ, completeNodes, fourthNode]

/-- The fixed universal pair specializes to the actual lifted rational function. -/
theorem universalLift_orbit (a b i : ℕ) (z : Fin 3 → Polynomial ℚ) :
    MvPolynomial.eval₂ (Int.castRingHom (RatFunc ℚ)) (orbitLiftInputs a b i z) universalLiftNumerator /
      MvPolynomial.eval₂ (Int.castRingHom (RatFunc ℚ)) (orbitLiftInputs a b i z) universalLiftDenominator =
        orbitLiftParameter a b i z := by
  let φ : MvPolynomial (Fin 10) ℤ →+* RatFunc ℚ :=
    MvPolynomial.eval₂Hom (Int.castRingHom (RatFunc ℚ)) (orbitLiftInputs a b i z)
  let ψ : MvPolynomial (Fin 3) ℚ →+* RatFunc ℚ :=
    (algebraMap (Polynomial ℚ) (RatFunc ℚ)).comp (MvPolynomial.aeval z).toRingHom
  have hc : φ ∘ universalLiftCofactors = ψ ∘ orbitCurveCofactorsQ a b i := by
    funext j
    exact universalLiftCofactors_orbit a b i z j
  change φ (cofactorLiftNumerator (X 9) universalLiftCofactors) /
    φ (cofactorLiftDenominator universalLiftCofactors) =
      ψ (cofactorLiftNumerator (C (a : ℚ)) (orbitCurveCofactorsQ a b i)) /
        ψ (cofactorLiftDenominator (orbitCurveCofactorsQ a b i))
  rw [map_cofactorLiftNumerator, map_cofactorLiftDenominator,
    map_cofactorLiftNumerator, map_cofactorLiftDenominator, hc]
  congr 2
  simp [φ, ψ, orbitLiftInputs]

end
end PierceLengthBound.FixedDividend
