/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionInitialForm
public import Mathlib.Algebra.DualNumber

/-! First jets of formal sections. Polynomial equations have the same
constant and linear coefficients on any two sections with matching first jets. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial
noncomputable section

/-- Truncation of a formal series modulo the square of its parameter. -/
def formalFirstJet {R : Type*} [CommRing R] : PowerSeries R →+* DualNumber R where
  toFun f := (show DualNumber R from (PowerSeries.constantCoeff f, PowerSeries.coeff 1 f))
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' f g := by
    apply TrivSqZeroExt.ext
    · change PowerSeries.constantCoeff (f + g) = _ + _
      exact map_add _ f g
    · change PowerSeries.coeff 1 (f + g) = _ + _
      exact map_add _ f g
  map_mul' f g := by
    apply TrivSqZeroExt.ext
    · change PowerSeries.constantCoeff (f * g) = _ * _
      exact map_mul _ f g
    · change PowerSeries.coeff 1 (f * g) =
        PowerSeries.constantCoeff f * PowerSeries.coeff 1 g +
          PowerSeries.coeff 1 f * PowerSeries.constantCoeff g
      simp [PowerSeries.coeff_one_mul, mul_comm, add_comm]

@[simp] lemma formalFirstJet_fst {R : Type*} [CommRing R] (f : PowerSeries R) :
    (formalFirstJet f).fst = PowerSeries.constantCoeff f := rfl

@[simp] lemma formalFirstJet_snd {R : Type*} [CommRing R] (f : PowerSeries R) :
    (formalFirstJet f).snd = PowerSeries.coeff 1 f := rfl

end
end PierceLengthBound.FixedDividend
