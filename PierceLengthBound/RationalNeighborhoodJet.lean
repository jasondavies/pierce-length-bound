/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import PierceLengthBound.RationalNeighborhood

/-! Rational dependence of the first two coefficients of formal paths. -/
@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

def RationalFirstJet {σ : Type*} (p : σ → ℚ) (f : (σ → ℚ) → PowerSeries ℚ) : Prop :=
  RationalNear p (fun x => PowerSeries.constantCoeff (f x)) ∧
    RationalNear p (fun x => PowerSeries.coeff 1 (f x))

namespace RationalFirstJet
variable {σ : Type*} {p : σ → ℚ} {f g : (σ → ℚ) → PowerSeries ℚ}

theorem constant (f : PowerSeries ℚ) : RationalFirstJet p (fun _ => f) :=
  ⟨RationalNear.constant _, RationalNear.constant _⟩

theorem C {f : (σ → ℚ) → ℚ} (hf : RationalNear p f) :
    RationalFirstJet p (fun x => PowerSeries.C (f x)) := by
  constructor
  · simpa using hf
  · simpa using RationalNear.constant (p := p) 0

theorem add (hf : RationalFirstJet p f) (hg : RationalFirstJet p g) :
    RationalFirstJet p (fun x => f x + g x) := by
  exact ⟨by simpa using hf.1.add hg.1, by simpa using hf.2.add hg.2⟩

theorem mul (hf : RationalFirstJet p f) (hg : RationalFirstJet p g) :
    RationalFirstJet p (fun x => f x * g x) := by
  refine ⟨by simpa using hf.1.mul hg.1, ?_⟩
  simpa only [PowerSeries.coeff_one_mul] using
    (hf.2.mul hg.1).add (hg.2.mul hf.1)

theorem polynomial {τ : Type*} (F : MvPolynomial τ ℚ)
    (g : (σ → ℚ) → τ → PowerSeries ℚ)
    (hg : ∀ j, RationalFirstJet p (fun x => g x j)) :
    RationalFirstJet p (fun x => MvPolynomial.eval₂Hom PowerSeries.C (g x) F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simpa using constant (p := p) (PowerSeries.C c)
  | add F G hF hG => simpa using hF.add hG
  | mul_X F j hF => simpa using hF.mul (hg j)

end RationalFirstJet
end
end PierceLengthBound.FixedDividend
