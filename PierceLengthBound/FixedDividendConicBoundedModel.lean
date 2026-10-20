/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendConicModelRepresentation

/-! Every actual nonexceptional degree-two component admits a bounded integral
parabolic equation in one of two coordinate orders. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial
set_option maxHeartbeats 1000000

/-- Uniform bounded integral plane model from common rational pattern
numerators. All discriminant and nonvanishing conclusions are proved from the
actual component geometry. -/
theorem nonexceptional_bounded_integer_conic_model
    (r u v r' u' v' D n0 n1 n2 e : ℤ) {M L : ℤ}
    (hM : 1 ≤ M) (hL : 0 ≤ L) (hD0 : D ≠ 0)
    (hr : |r| ≤ M) (hu : |u| ≤ M) (hv : |v| ≤ M)
    (hr' : |r'| ≤ M) (hu' : |u'| ≤ M) (hv' : |v'| ≤ M) (hD : |D| ≤ M)
    (hn0 : |n0| ≤ L) (hn1 : |n1| ≤ L) (hn2 : |n2| ≤ L) (he : |e| ≤ L)
    (hρpos : 0 < (r : ℚ) / D) (hupos : 0 < (u : ℚ) / D)
    (hvneg : (v : ℚ) / D < 0)
    (hne : NonexceptionalPattern (((r : ℚ) / D : ℚ) : ℝ)
      (((u : ℚ) / D : ℚ) : ℝ) (((v : ℚ) / D : ℚ) : ℝ))
    (A a : ℚ) (hA : A ≠ 0) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic ((r : ℚ) / D) ((u : ℚ) / D) ((v : ℚ) / D)
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) ∈ I)
    (hg : curveEquation ((r : ℚ) / D) ((u : ℚ) / D) ((v : ℚ) / D)
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) A a ∈ I)
    (hn : n0 ≠ 0 ∨ n1 ≠ 0 ∨ n2 ≠ 0)
    (hplane : C (n0 : ℚ) * X 0 + C (n1 : ℚ) * X 1 + C (n2 : ℚ) * X 2 +
      C (e : ℚ) ∈ I)
    {N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = 2 * n + b)
    (x : Fin 3 → ℚ) (hx : x ∈ coordinateZeroLocus I) :
    ∃ (j k : Fin 3) (c : Fin 6 → ℤ), Function.Bijective ![j, 0, k] ∧
      (![n0, n1, n2] : Fin 3 → ℤ) k ≠ 0 ∧
      (∀ i, |c i| ≤ 10 * (12 * M ^ 2) ^ 2 * L ^ 2) ∧
      c 0 ≠ 0 ∧ (c 1) ^ 2 - 4 * c 0 * c 2 = 0 ∧
      2 * c 1 * c 3 - 4 * c 0 * c 4 ≠ 0 ∧
      ∀ z : Fin 3 → ℤ, (fun i => (z i : ℚ)) ∈ coordinateZeroLocus I →
        conicValue (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (z j) (z 0) = 0 := by
  let w := ternaryNumerators r u v r' u' v' D
  have hw : ∀ j, |w j| ≤ 12 * M ^ 2 :=
    ternaryNumerators_height hM hr hu hv hr' hu' hv' hD
  have hB : 1 ≤ 12 * M ^ 2 := by nlinarith
  have hDb : |D| ≤ 12 * M ^ 2 := by nlinarith
  by_cases hp2 : n2 ≠ 0
  · have hp2q : (n2 : ℚ) ≠ 0 := by exact_mod_cast hp2
    let V := rationalPlaneConicCoefficients ((r : ℚ) / D) ((u : ℚ) / D) ((v : ℚ) / D)
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) n0 n1 n2 e
    have hgeo := rational_nonexceptional_parabolic_model hρpos hupos hvneg hne
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) A a hA ha I hf hg
      n0 n1 n2 e hp2q hplane hdegree x hx
    have hrep := first_conic_ternary_representation r u v r' u' v' D n0 n1 n2 e hD0
    have hp := integralPlaneConicCoefficients_parabolic
      (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) D n0 n1 n2 e hD0 hp2 V
      (congrFun hrep) hgeo.1 hgeo.2.1 hgeo.2.2.1
    refine ⟨1, 2, _, by decide, hp2, ?_, hp.1, hp.2.1, hp.2.2.1, ?_⟩
    · exact integralPlaneConicCoefficients_height hB hL
        (hw 0) (hw 1) (hw 2) hDb (hw 3) (hw 4) (hw 5) hn0 hn1 hn2 he
    · intro z hz
      exact hp.2.2.2 _ _ (hgeo.2.2.2.2 _ hz)
  · have hnp : (n0 : ℚ) ≠ 0 ∨ (n1 : ℚ) ≠ 0 ∨ (n2 : ℚ) ≠ 0 := by
      exact_mod_cast hn
    have hp1q := (rational_nonexceptional_plane_pivot hρpos hupos hvneg hne
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) A a ha I hf hg
      n0 n1 n2 e hnp hplane (by decide : 0 < 2) hdegree).resolve_right (by
        intro hh
        exact hp2 (by exact_mod_cast hh))
    have hp1 : n1 ≠ 0 := by exact_mod_cast hp1q
    let V := rationalSecondPlaneConicCoefficients
      ((r : ℚ) / D) ((u : ℚ) / D) ((v : ℚ) / D)
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) n0 n1 n2 e
    have hgeo := rational_nonexceptional_second_parabolic_model hρpos hupos hvneg hne
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) A a hA ha I hf hg
      n0 n1 n2 e hp1q hplane hdegree x hx
    have hrep := second_conic_ternary_representation r u v r' u' v' D n0 n1 n2 e hD0
    have hp := integralPlaneConicCoefficients_parabolic
      (w 0) (w 2) (w 1) (w 3) (w 5) (w 4) D n0 n2 n1 e hD0 hp1 V
      (congrFun hrep) hgeo.1 hgeo.2.1 hgeo.2.2.1
    refine ⟨2, 1, _, by decide, hp1, ?_, hp.1, hp.2.1, hp.2.2.1, ?_⟩
    · exact integralPlaneConicCoefficients_height hB hL
        (hw 0) (hw 2) (hw 1) hDb (hw 3) (hw 5) (hw 4) hn0 hn2 hn1 he
    · intro z hz
      exact hp.2.2.2 _ _ (hgeo.2.2.2.2 _ hz)

end
end PierceLengthBound.FixedDividend
