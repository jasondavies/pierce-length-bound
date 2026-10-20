/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendInfinitySection

/-!
# Regularity of a linear coordinate on the infinity section

When a linear coordinate generates the next graded piece and the Hilbert
function has reached its linear range, it cannot kill a nonzero element of the
previous graded piece. This finite-dimensional argument will identify the
section's stable graded dimension with its affine-chart dimension.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Exact dimension growth turns graded surjectivity into graded injectivity. -/
theorem linear_map_inf_eq_of_dimensions {K A : Type*} [Field K]
    [AddCommGroup A] [Module K A] (U V W : Submodule K A)
    [Module.Finite K U] [Module.Finite K V] [Module.Finite K W]
    (L : A →ₗ[K] A) (hL : Function.Injective L)
    (hUV : U ≤ V) (hLU : U.map L ≤ V)
    (hspan : V ⊔ V.map L = W)
    (hdim : Module.finrank K W + Module.finrank K U = 2 * Module.finrank K V) :
    V ⊓ V.map L = U.map L := by
  have hle : U.map L ≤ V ⊓ V.map L := le_inf hLU (Submodule.map_mono hUV)
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hmU := (Submodule.equivMapOfInjective L hL U).finrank_eq
  have hmV := (Submodule.equivMapOfInjective L hL V).finrank_eq
  have hs := Submodule.finrank_sup_add_finrank_inf_eq V (V.map L)
  rw [hspan] at hs
  omega

/-- Strictness of multiplication in the stable Hilbert range. -/
theorem filtered_linear_coordinate_strict {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (l : MvPolynomial σ K ⧸ I) (hl : l ∈ filteredCoordinateSpace I 1) (hl0 : l ≠ 0)
    {d N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    {n : ℕ} (hn : N ≤ n)
    (hspan : filteredCoordinateSpace I (n + 1) ⊔
        (filteredCoordinateSpace I (n + 1)).map (LinearMap.mulLeft K l) =
      filteredCoordinateSpace I (n + 2))
    {a : MvPolynomial σ K ⧸ I}
    (ha : a ∈ filteredCoordinateSpace I (n + 1))
    (hla : l * a ∈ filteredCoordinateSpace I (n + 1)) :
    a ∈ filteredCoordinateSpace I n := by
  have hd0 := hdegree n hn
  have hd1 := hdegree (n + 1) (by omega)
  have hd2 := hdegree (n + 2) (by omega)
  have hdim : Module.finrank K (filteredCoordinateSpace I (n + 2)) +
      Module.finrank K (filteredCoordinateSpace I n) =
      2 * Module.finrank K (filteredCoordinateSpace I (n + 1)) := by
    push_cast at hd1 hd2
    nlinarith
  have he := linear_map_inf_eq_of_dimensions
    (filteredCoordinateSpace I n) (filteredCoordinateSpace I (n + 1))
    (filteredCoordinateSpace I (n + 2)) (LinearMap.mulLeft K l)
    (fun _ _ h => mul_left_cancel₀ hl0 h)
    (filteredCoordinateSpace_mono I (by omega)) (by
      rintro x ⟨y, hy, rfl⟩
      simpa only [LinearMap.mulLeft_apply, Nat.add_comm] using
        filteredCoordinateSpace_mul_mem I hl hy)
    hspan hdim
  have hmem : l * a ∈ filteredCoordinateSpace I (n + 1) ⊓
      (filteredCoordinateSpace I (n + 1)).map (LinearMap.mulLeft K l) :=
    ⟨hla, ⟨a, ha, rfl⟩⟩
  rw [he] at hmem
  obtain ⟨a', ha', heq⟩ := hmem
  have haa : a' = a := mul_left_cancel₀ hl0 heq
  rw [← haa]
  exact ha'

/-- Iterating strictness removes every artificial power of the chart coordinate.
This is the saturation statement needed for injectivity of the chart section. -/
theorem filtered_linear_coordinate_saturation {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (l : MvPolynomial σ K ⧸ I) (hl : l ∈ filteredCoordinateSpace I 1) (hl0 : l ≠ 0)
    {d N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (hspan : ∀ n ≥ N, filteredCoordinateSpace I (n + 1) ⊔
        (filteredCoordinateSpace I (n + 1)).map (LinearMap.mulLeft K l) =
      filteredCoordinateSpace I (n + 2))
    {n : ℕ} (hn : N ≤ n) (k : ℕ) {a : MvPolynomial σ K ⧸ I}
    (ha : a ∈ filteredCoordinateSpace I (n + 1))
    (hla : l ^ k * a ∈ filteredCoordinateSpace I (n + k)) :
    a ∈ filteredCoordinateSpace I n := by
  induction k generalizing n a with
  | zero => simpa using hla
  | succ k ih =>
    have hla1 : l * a ∈ filteredCoordinateSpace I ((n + 1) + 1) := by
      simpa only [Nat.add_comm] using filteredCoordinateSpace_mul_mem I hl ha
    have hh : l ^ k * (l * a) ∈ filteredCoordinateSpace I ((n + 1) + k) := by
      simpa only [pow_succ, mul_assoc,
        show (n + 1) + k = n + (k + 1) by omega] using hla
    have hla2 := ih (n := n + 1) (by omega) hla1 hh
    exact filtered_linear_coordinate_strict I l hl hl0 hdegree hn (hspan n hn) ha hla2

end
end PierceLengthBound.FixedDividend
