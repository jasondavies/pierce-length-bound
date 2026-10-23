/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic

/-! The algebraic witness underlying the factor-resolvent reduction.
A proper factor of an irreducible polynomial cannot have all coefficients
in the base field. A coefficient outside that field has an irreducible
minimal polynomial of degree at least two, providing the required saving
when its integral specializations are counted. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- A nonconstant proper monic factor over an extension has a genuinely
nonrational coefficient. No separability assumption is needed. -/
theorem branch_proper_factor_has_nonrational_coefficient
    {p : F[X]} (hp : Irreducible p) {q : L[X]} (hq : q.Monic)
    (hdiv : q ∣ p.map (algebraMap F L))
    (hqpos : 0 < q.natDegree) (hqlt : q.natDegree < p.natDegree) :
    ∃ j : ℕ, q.coeff j ∉ Set.range (algebraMap F L) := by
  classical
  by_contra! hc
  have hlift : q ∈ Polynomial.lifts (algebraMap F L) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr hc
  obtain ⟨q₀, hmap, hdegree, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hq
  have hdiv₀ : q₀ ∣ p := (Polynomial.map_dvd_map' (algebraMap F L)).mp (hmap ▸ hdiv)
  obtain hunit | hassoc := hp.dvd_iff.mp hdiv₀
  · have hz := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  · have hdeg := Polynomial.natDegree_le_of_dvd hassoc.dvd hmonic.ne_zero
    omega

/-- Every such proper factor supplies an irreducible algebraic coefficient
equation with root-variable degree at least two. -/
theorem branch_proper_factor_minpoly_witness
    {p : F[X]} (hp : Irreducible p) (hpmonic : p.Monic)
    {q : L[X]} (hq : q.Monic) (hdiv : q ∣ p.map (algebraMap F L))
    (hqpos : 0 < q.natDegree) (hqlt : q.natDegree < p.natDegree) :
    ∃ j : ℕ, Irreducible (minpoly F (q.coeff j)) ∧
      2 ≤ (minpoly F (q.coeff j)).natDegree ∧
      aeval (q.coeff j) (minpoly F (q.coeff j)) = 0 := by
  obtain ⟨j, hj⟩ := branch_proper_factor_has_nonrational_coefficient hp hq hdiv hqpos hqlt
  have hint := Polynomial.isIntegral_coeff_of_dvd p q hpmonic hq hdiv j
  refine ⟨j, minpoly.irreducible hint, ?_, minpoly.aeval F (q.coeff j)⟩
  exact (minpoly.two_le_natDegree_iff hint).mpr hj

end
end PierceLengthBound.FixedDividend
