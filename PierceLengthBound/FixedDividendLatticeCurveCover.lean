/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendLatticeCoordinates
public import PierceLengthBound.FixedDividendRationalOrbit

/-! Transfer actual integer gap points and their rational curve cover to a small
integer box, retaining primality and the exact affine Hilbert degree. -/

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

/-- A rational prime-curve cover of bounded gap vectors transfers to a box of
radius `floor(3H/shortR p)`. Its number of components does not increase, and
all affine Hilbert degrees are preserved exactly. -/
theorem lattice_curve_cover {p : Fin 10 → ℤ} {H : ℕ} {V : Finset (Fin 5 → ℤ)}
    (hV : V.Nonempty) (h0 : p 0 ≠ 0)
    (hVs : ∀ k ∈ V, (∀ j, |k j| ≤ H) ∧
      ∃ M : Fin 3 → Fin 5 → ℤ, plk M = p ∧ ∀ j, M 1 j = k j)
    (S : Finset (Ideal (MvPolynomial (Fin 3) ℚ)))
    (hcover : ∀ k ∈ V, ∃ I ∈ S,
      (fun j => (gapNodes k j : ℚ)) ∈ coordinateZeroLocus I) :
    ∃ (y : (Fin 5 → ℤ) → Fin 3 → ℤ)
      (S' : Finset (Ideal (MvPolynomial (Fin 3) ℚ))),
      Set.InjOn y V ∧ S'.card ≤ S.card ∧
      (∀ k ∈ V, (∀ j, |y k j| ≤ (3 * H / shortR p : ℕ)) ∧
        ∃ J ∈ S', (fun j => (y k j : ℚ)) ∈ coordinateZeroLocus J) ∧
      ∀ J ∈ S', ∃ I ∈ S,
        (I.IsPrime → J.IsPrime) ∧
        ∀ n, Module.finrank ℚ (filteredCoordinateSpace J n) =
          Module.finrank ℚ (filteredCoordinateSpace I n) := by
  obtain ⟨B, y, hB, hy, hnodes⟩ := lattice_node_coordinates hV h0 hVs
  let C : Matrix (Fin 3) (Fin 3) ℚ := fun i j => (B i j : ℚ)
  have hC : C.det ≠ 0 := by
    change (B.map (fun x => (x : ℚ))).det ≠ 0
    rw [← Int.cast_det]
    exact_mod_cast hB
  obtain ⟨S', hcard, hcover', hpre⟩ := matrix_coordinate_component_cover C hC S
  refine ⟨y, S', hy, hcard, ?_, ?_⟩
  · intro k hk
    refine ⟨(hnodes k hk).1, (hcover' _).mpr ?_⟩
    obtain ⟨I, hI, hx⟩ := hcover k hk
    refine ⟨I, hI, ?_⟩
    have he : (fun j => (gapNodes k j : ℚ)) = C *ᵥ (fun j => (y k j : ℚ)) := by
      rw [(hnodes k hk).2]
      exact integer_matrix_mulVec_cast B (y k)
    rwa [← he]
  · intro J hJ
    obtain ⟨I, hI, rfl⟩ := hpre J hJ
    refine ⟨I, hI, fun hIprime => ?_, ?_⟩
    · let := hIprime
      exact matrix_coordinate_prime C hC I
    · exact nonsingular_matrix_filtered_finrank C hC I

/-- Integer points in the transferred cover retain the same explicit degree
range as the original components. -/
theorem lattice_curve_cover_degree_range {p : Fin 10 → ℤ} {H lo hi : ℕ}
    {V : Finset (Fin 5 → ℤ)} (hV : V.Nonempty) (h0 : p 0 ≠ 0)
    (hVs : ∀ k ∈ V, (∀ j, |k j| ≤ H) ∧
      ∃ M : Fin 3 → Fin 5 → ℤ, plk M = p ∧ ∀ j, M 1 j = k j)
    (S : Finset (Ideal (MvPolynomial (Fin 3) ℚ)))
    (hcover : ∀ k ∈ V, ∃ I ∈ S,
      (fun j => (gapNodes k j : ℚ)) ∈ coordinateZeroLocus I)
    (hdeg : ∀ I ∈ S, I.IsPrime ∧ ∃ d : ℕ, lo ≤ d ∧ d ≤ hi ∧
      ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
        (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    ∃ (y : (Fin 5 → ℤ) → Fin 3 → ℤ)
      (S' : Finset (Ideal (MvPolynomial (Fin 3) ℚ))),
      Set.InjOn y V ∧ S'.card ≤ S.card ∧
      (∀ k ∈ V, (∀ j, |y k j| ≤ (3 * H / shortR p : ℕ)) ∧
        ∃ J ∈ S', (fun j => (y k j : ℚ)) ∈ coordinateZeroLocus J) ∧
      ∀ J ∈ S', J.IsPrime ∧ ∃ d : ℕ, lo ≤ d ∧ d ≤ hi ∧
        ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace J n) : ℤ) = (d : ℤ) * n + c := by
  obtain ⟨y, S', hy, hcard, hcover', htrans⟩ := lattice_curve_cover hV h0 hVs S hcover
  refine ⟨y, S', hy, hcard, hcover', ?_⟩
  intro J hJ
  obtain ⟨I, hI, hprime, hdim⟩ := htrans J hJ
  obtain ⟨hIp, d, hlo, hhi, N, c, hd⟩ := hdeg I hI
  refine ⟨hprime hIp, d, hlo, hhi, N, c, ?_⟩
  intro n hn
  rw [hdim]
  exact hd n hn

end
end PierceLengthBound.FixedDividend
