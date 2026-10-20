/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchFamilyDegree

/-! Algebra structures on a family selecting between two branch models.
Explicit instances keep the selected ring and its field embedding compatible. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
universe u

def branchModelSum (R S : Type u) {ι κ : Type*} : ι ⊕ κ → Type u
  | .inl _ => R
  | .inr _ => S

namespace branchModelSum
variable {R S : Type u} {ι κ : Type*}

instance [CommRing R] [CommRing S] (k : ι ⊕ κ) : CommRing (branchModelSum R S k) :=
  match k with | .inl _ => inferInstanceAs (CommRing R) | .inr _ => inferInstanceAs (CommRing S)

instance [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S] (k : ι ⊕ κ) :
    IsDedekindDomain (branchModelSum R S k) :=
  match k with
  | .inl _ => inferInstanceAs (IsDedekindDomain R)
  | .inr _ => inferInstanceAs (IsDedekindDomain S)

instance [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S] (k : ι ⊕ κ) :
    Algebra ℚ (branchModelSum R S k) :=
  match k with | .inl _ => inferInstanceAs (Algebra ℚ R) | .inr _ => inferInstanceAs (Algebra ℚ S)

instance {F : Type*} [CommRing R] [CommRing S] [Field F] [Algebra R F] [Algebra S F]
    (k : ι ⊕ κ) : Algebra (branchModelSum R S k) F :=
  match k with | .inl _ => inferInstanceAs (Algebra R F) | .inr _ => inferInstanceAs (Algebra S F)

instance {F : Type*} [CommRing R] [CommRing S] [Field F] [Algebra ℚ R] [Algebra ℚ S]
    [Algebra ℚ F] [Algebra R F] [Algebra S F]
    [IsScalarTower ℚ R F] [IsScalarTower ℚ S F] (k : ι ⊕ κ) :
    IsScalarTower ℚ (branchModelSum R S k) F :=
  match k with
  | .inl _ => inferInstanceAs (IsScalarTower ℚ R F)
  | .inr _ => inferInstanceAs (IsScalarTower ℚ S F)

instance {F : Type*} [CommRing R] [CommRing S] [Field F] [Algebra R F] [Algebra S F]
    [IsFractionRing R F] [IsFractionRing S F] (k : ι ⊕ κ) :
    IsFractionRing (branchModelSum R S k) F :=
  match k with
  | .inl _ => inferInstanceAs (IsFractionRing R F)
  | .inr _ => inferInstanceAs (IsFractionRing S F)

end branchModelSum
end PierceLengthBound.FixedDividend
