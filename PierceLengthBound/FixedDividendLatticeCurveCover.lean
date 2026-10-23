/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendLatticeCoordinates
public import PierceLengthBound.FixedDividendRationalOrbit

/-! Casts identifying integer gap points and their integer matrix images with the rational
orbit nodes, used to transfer rational curve covers to lattice coordinates. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset Matrix

lemma gapNodes_kap (a b i : ℕ) :
    (fun j => (gapNodes (kap a b i) j : ℚ)) = orbitFreeNodesQ a b i := by
  funext j
  fin_cases j <;> simp [gapNodes, kap, kq, orbitFreeNodesQ, Nat.add_assoc]

lemma integer_matrix_mulVec_cast (B : Matrix (Fin 3) (Fin 3) ℤ) (y : Fin 3 → ℤ) :
    (fun j => ((B *ᵥ y) j : ℚ)) =
      (fun i j => (B i j : ℚ)) *ᵥ (fun j => (y j : ℚ)) := by
  ext j
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end
end PierceLengthBound.FixedDividend
